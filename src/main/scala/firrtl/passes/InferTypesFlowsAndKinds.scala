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
    val lut = new Lookup(replaceUnknowns, moduleTypes)
    m.map(onPort(_)(lut)).map(onStmt(_)(lut))
  }

  private def onPort(p: Port)(implicit lut: Lookup): Port = {
    p.copy(tpe = lut.declare(p.name, p.tpe, PortKind))
  }

  private def onStmt(s: Statement)(implicit lut: Lookup): Statement = s match {
    case sx: DefInstance =>
      sx.copy(tpe = lut.declare(sx.name, lut.moduleTypes(sx.name), InstanceKind))
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
    * @note Type propagates bottom-up, a->b->c for `a.b.c`.
    *       This is why the `lut` needs to operate on already visited expressions.
    * @note Flow propagates top-down, c->b->a for `a.b.c` (which will be represented as `(((a) b) c)`).
    *       Flow also relies on Type in that it needs to know the Field type in order to determine
    *       whether a field is flipped.
    *       In order to reconcile the opposite propagation and the co-dependence, we remember
    *       all field names that were used to access a Reference (`fieldTrace`) which allows us to resolve
    *       the Flow at the leaf node and then propagate it bottom up,
    * @note Kind only matters at the Reference leaf nodes.
    */
  private def onExpr(f: Flow, fieldTrace: List[String])(expr: Expression)(implicit lut: Lookup): Expression = {
    val subTrace = expr match {
      case SubField(_, name, _, _) => fieldTrace :+ name
      case _ => fieldTrace
    }
    expr.map(onExpr(f, subTrace)) match {
      case e: Reference => lut.reference(e.name, f)
      case e: SubField => lut.subField(e.expr, e.name, f)
      case e: SubIndex => lut.subIndex(e.expr, e.value, f)
      case e: SubAccess => lut.subAccess(e.expr, e.index, f)
      // type inference for non-reference expressions
      case e: DoPrim => e.copy(tpe = e.op.propagateType(e))
      case e: Mux => e.copy(tpe = Utils.mux_type_and_widths(e.tval, e.fval))
      case e: ValidIf => e.copy(tpe = e.value.tpe)
      case e: UIntLiteral => e
      case e: SIntLiteral => e
    }
  }
  //scalastyle:on cyclomatic.complexity
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
    maps(SourceFlow).refs(name) = Reference(name, t, kind, SourceFlow)
    maps(SinkFlow).refs(name) = Reference(name, t, kind, SinkFlow)
    t
  }

  // Access the unique accessor expressions.
  // Note that sub accesses will only work if you first resolve the expressions in them.
  def reference(name: String, flow: Flow): Reference = maps(flow).refs(name)
  def subField(expr: Expression, name: String, flow: Flow): SubField =
    maps(flow).field.getOrElseUpdate(IdAndEqKey(expr, name),
      SubField(expr, name, Utils.field_type(expr.tpe, name), flow))
  def subIndex(expr: Expression, index: Int, flow: Flow): SubIndex =
    maps(flow).index.getOrElseUpdate(IdAndEqKey(expr, index),
      SubIndex(expr, index, Utils.sub_type(expr.tpe), flow))
  def subAccess(expr: Expression, index: Expression, flow: Flow): SubAccess =
    maps(flow).access.getOrElseUpdate(IdSeqKey(Seq(expr, index)),
      SubAccess(expr, index, Utils.sub_type(expr.tpe), flow))

  // Expose the replace type functionality in order to handle the DefMemory special case.
  def replaceUnknowns(tpe: Type): Type = replace(tpe)

  // Remember expressions in order to ensure that objects are interned as much as possible.
  private class Maps {
    val refs   = mutable.HashMap[String, Reference]()
    val field  = mutable.HashMap[IdAndEqKey[Expression, String], SubField]()
    val index  = mutable.HashMap[IdAndEqKey[Expression, Int], SubIndex]()
    val access = mutable.HashMap[IdSeqKey[Expression], SubAccess]()
  }
  private val maps: Map[Flow, Maps] = Seq(SourceFlow -> new Maps(), SinkFlow -> new Maps()).toMap
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
  }
}