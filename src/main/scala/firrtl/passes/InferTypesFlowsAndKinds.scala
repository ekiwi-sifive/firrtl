// See LICENSE for license details.

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.stage.TransformManager.TransformDependency

import scala.collection.mutable

/** This pass infers the types, flows and kinds of all expressions.
  * Unknown widths are replaced with variable widths which can be resolved
  * by the InferWidths pass.
  *
  * TODO: make this work for Chirrtl as well.
  *
  * TODO: why does the old InferTypes pass not call remove_unknown on module types?
  */
object InferTypesFlowsAndKinds extends Pass {
  override def prerequisites: Seq[TransformDependency] = firrtl.stage.Forms.WorkingIR
  override def invalidates(a: Transform): Boolean = false

  override def run(c: Circuit): Circuit = {
    // The Width and Bound variables are in a global namespace separate from the Wire, Node etc. names.
    val replaceUnknowns = new ReplaceUnknowns(Namespace())

    // Module types are global and needed at all DefInstance sites.
    val moduleTypes = c.modules.map(m => m.name -> replaceUnknowns(Utils.module_type(m))).toMap

    c.mapModule(onModule(replaceUnknowns, moduleTypes))
  }

  private def onModule(replaceUnknowns: ReplaceUnknowns, moduleTypes: Map[String, Type])(m: DefModule): DefModule = {
    implicit val lut: Lookup = new Lookup(replaceUnknowns, moduleTypes)
    m.map(onPort).map(onStmt)
  }

  private def onPort(p: Port)(implicit lut: Lookup): Port = {
    p.copy(tpe = lut.declare(p.name, p.tpe, PortKind))
  }

  private def onStmt(s: Statement)(implicit lut: Lookup): Statement = s match {
    case sx: DefInstance =>
      sx.copy(tpe = lut.declare(sx.name, lut.moduleTypes(sx.module), InstanceKind))
    case sx: DefWire =>
      sx.copy(tpe = lut.declare(sx.name, sx.tpe, WireKind))
    case sx: DefNode =>
      val value = onExpr(SourceFlow)(sx.value)
      lut.declare(sx.name, value.tpe, NodeKind)
      sx.copy(value = value)
    case sx: DefRegister =>
      sx.copy(tpe = lut.declare(sx.name, sx.tpe, RegKind)).map(onExpr(SourceFlow))
    case sx: DefMemory =>
      // all ports referring to the datatype need to be inferred to the same width
      val noUnknowns = sx.copy(dataType = lut.replaceUnknowns(sx.dataType))
      lut.declare(sx.name, MemPortUtils.memType(noUnknowns), MemKind)
      noUnknowns
    case sx: IsInvalid =>
      sx.copy(expr = onExpr(SinkFlow)(sx.expr))
    case sx: Connect =>
      sx.copy(loc = onExpr(SinkFlow)(sx.loc), expr = onExpr(SourceFlow)(sx.expr))
    case sx: PartialConnect =>
      sx.copy(loc = onExpr(SinkFlow)(sx.loc), expr = onExpr(SourceFlow)(sx.expr))
    // TODO: should we do anything special for Attach here? DuplexFlow?
    case sx =>
      sx.map(onExpr(SourceFlow)).map(onStmt)
  }

  //scalastyle:off cyclomatic.complexity
  /** Replace all expressions with their typed, known-flow and known-kind versions.
    * @note Type propagates bottom-up / left-to-right, e.g., a->b->c for `a.b.c`.
    *       This is why the `lut` needs to operate on already visited expressions.
    * @note Flow propagates top-down / right-to-left, e.g., c->b->a for `a.b.c`
    *       (which will be represented as `(((a) b) c)`).
    *       Flow also relies on Type in that it needs to know the Field type in order to determine
    *       whether a field is flipped.
    *       In order to reconcile the opposite propagation and the co-dependence, we remember
    *       all field names that were used to access a Reference (`fieldTrace`) which allows us to
    *       resolve the Flow at the leaf node.
    * @note Kind only matters at the Reference leaf nodes.
    */
  private def onExpr(f: Flow, fieldTrace: List[String] = List())(expr: Expression)(implicit lut: Lookup): Expression = {
    val subTrace = expr match {
      case SubField(_, name, _, _) => name +: fieldTrace
      case _ => fieldTrace
    }
    expr.map(onExpr(f, subTrace)) match {
      case e: Reference =>
        val base = lut.reference(e.name, f)
        if(fieldTrace.nonEmpty && isFlipped(base.tpe, fieldTrace)) {
          lut.reference(e.name, flip(f))
        } else { base }
      case e: SubField =>
        val fieldType = Utils.field_type(e.expr.tpe, e.name)
        val flow = if(fieldTrace.nonEmpty && isFlipped(fieldType, fieldTrace)) { flip(f) } else { f }
        lut.subField(e.expr, e.name, flow)
      case e: SubIndex =>
        val dataType = Utils.sub_type(e.expr.tpe)
        val flow = if(fieldTrace.nonEmpty && isFlipped(dataType, fieldTrace)) { flip(f) } else { f }
        lut.subIndex(e.expr, e.value, flow)
      case e: SubAccess =>
        val dataType = Utils.sub_type(e.expr.tpe)
        val flow = if(fieldTrace.nonEmpty && isFlipped(dataType, fieldTrace)) { flip(f) } else { f }
        lut.subAccess(e.expr, e.index, flow)
      // type inference for non-reference expressions
      case e: DoPrim => e.copy(tpe = e.op.propagateType(e))
      case e: Mux => e.copy(tpe = Utils.mux_type_and_widths(e.tval, e.fval))
      case e: ValidIf => e.copy(tpe = e.value.tpe)
      case e: UIntLiteral => e
      case e: SIntLiteral => e
    }
  }
  //scalastyle:on cyclomatic.complexity

  private def flip(o: Flow): Flow = o match {
    case SourceFlow => SinkFlow
    case SinkFlow => SourceFlow
  }

  private def isFlipped(tpe: Type, fieldTrace: List[String]): Boolean = tpe match {
    case BundleType(fields) =>
      val field = fields.find(_.name == fieldTrace.head).get
      isFlipped(field.tpe, fieldTrace.tail) ^ (field.flip == Flip)
    case VectorType(tpe, _) => isFlipped(tpe, fieldTrace)
    case _ => assert(fieldTrace.isEmpty) ; false
  }
}

/** Keeps track of all reference and accessor types, kinds and flows inside one module.
  *
  * In order to save memory, we only ever create a single unique
  * Reference or Sub{Access,Index,Field} (we are interning them).
  *
  * */
private class Lookup(replace: ReplaceUnknowns, val moduleTypes: Map[String, Type]) {
  def declare(name: String, tpe: Type, kind: Kind): Type = {
    val t = replaceUnknowns(tpe)
    // We eagerly generate all possible references for both, the lvalue (SinkFlow) and rvalue (SourceFlow) cases.
    refs(SourceFlow)(name) = Reference(name, t, kind, SourceFlow)
    refs(SinkFlow)(name) = Reference(name, t, kind, SinkFlow)
    t
  }

  // Access the unique accessor expressions.
  // Note that sub accesses will only work if you first resolve the expressions in them.
  def reference(name: String, flow: Flow): Reference = refs(flow)(name)
  def subField(expr: Expression, name: String, flow: Flow): SubField =
    fields.getOrElseUpdate(IdAndEqKey(expr, (flow, name)),
      SubField(expr, name, Utils.field_type(expr.tpe, name), flow))
  def subIndex(expr: Expression, index: Int, flow: Flow): SubIndex =
    indices.getOrElseUpdate(IdAndEqKey(expr, (flow, index)),
      SubIndex(expr, index, Utils.sub_type(expr.tpe), flow))
  def subAccess(expr: Expression, index: Expression, flow: Flow): SubAccess =
    accesses.getOrElseUpdate(IdSeqAndEqKey(Seq(expr, index), flow),
      SubAccess(expr, index, Utils.sub_type(expr.tpe), flow))

  // Expose the replace type functionality in order to handle the DefMemory special case.
  def replaceUnknowns(tpe: Type): Type = replace(tpe)

  // Remember expressions in order to ensure that objects are interned as much as possible.
  private val fields = mutable.HashMap[IdAndEqKey[Expression, (Flow, String)], SubField]()
  private val indices = mutable.HashMap[IdAndEqKey[Expression, (Flow, Int)], SubIndex]()
  private val accesses = mutable.HashMap[IdSeqAndEqKey[Expression, Flow], SubAccess]()
  private type RefMap = mutable.HashMap[String, Reference]
  private val refs: Map[Flow, RefMap] = Seq(SourceFlow -> new RefMap(), SinkFlow -> new RefMap()).toMap
}

/** Substitutes Unknown Width and Bound with unique variables. */
private class ReplaceUnknowns(namespace: Namespace) {
  private def apply(b: Bound): Bound = b match {
    case UnknownBound => VarBound(namespace.newName("b"))
    case k => k
  }
  private def apply(w: Width): Width = w match {
    case UnknownWidth => VarWidth(namespace.newName("w"))
    case wx => wx
  }
  def apply(t: Type): Type = t.mapType(apply).mapWidth(apply) match {
    case i: IntervalType => i.copy(lower = apply(i.lower), upper = apply(i.upper))
    case x => x
  }
}