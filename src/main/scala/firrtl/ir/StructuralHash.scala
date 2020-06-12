// See LICENSE for license details.

package firrtl.ir
import firrtl.passes.memlib.DefAnnotatedMemory
import firrtl.{DescribedStmt, DocString, EmptyDescription, MInfer, MRead, MReadWrite, MWrite, PrimOps, VRandom}

import java.nio.ByteBuffer
import java.security.MessageDigest
import scala.collection.mutable

/**
  * This object can performs a "structural" hash over any FirrtlNode.
  * It ignore:
  * - `Expression` types
  * - Any `Info` fields
  *
  * Please note that module hashes don't include any submodules by default.
  * Thus if you need the hash to change if a submodule changes, make sure to
  * use the `transitive` functions.
  *
  * @author Kevin Laeufer <laeufer@cs.berkeley.edu>
  * */
object StructuralHash {
  def md5(node: FirrtlNode): Array[Byte] = {
    val m = MessageDigest.getInstance("MD5")
    h(node)(m, EmptyMods)
    m.digest()
  }

  def transitiveMd5(name: String, modules: Seq[DefModule]): Array[Byte] = {
    val m = MessageDigest.getInstance("MD5")
    transitiveH(name, modules, m)
    m.digest()
  }

  private def transitiveH(name: String, modules: Seq[DefModule], m: MessageDigest): Unit = {
    val nameToMod = modules.map(m => m.name -> m).toMap
    // using Seq instead of Set for stability (if the order gets messed up the hash will be different
    var todo = Seq(name)
    var done = Seq[String]()
    while(todo.nonEmpty) {
      val mods = ModsArray()
      todo.foreach{ n =>
        val mod = nameToMod.getOrElse(n, throw new RuntimeException(s"Module $n cannot be found!"))
        h(mod)(m, mods)
      }
      done = done ++ todo
      todo = mods.a -- done
    }
  }

  @inline
  private def id(b: Byte)(implicit m: MessageDigest): Unit = m.update(b)
  @inline
  private def h(i: Int)(implicit m: MessageDigest): Unit =
    m.update(ByteBuffer.allocate(4).putInt(i).array())
  @inline
  private def h(d: Double)(implicit m: MessageDigest): Unit =
    m.update(ByteBuffer.allocate(8).putDouble(d).array())
  @inline
  private def h(i: BigInt)(implicit m: MessageDigest): Unit = m.update(i.toByteArray)
  @inline
  private def h(b: Boolean)(implicit m: MessageDigest): Unit = if(b) id(1) else id(0)
  @inline
  private def h(s: String)(implicit m: MessageDigest): Unit = m.update(s.getBytes()) // encoding should not matter

  // use to keep track of instanciated sub modules for transitive hashing
  private trait Mods { def add(n : String): Unit }
  private case object EmptyMods extends Mods { override def add(n: String): Unit = {} }
  private case class ModsArray(a: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()) extends Mods {
    override def add(n: String): Unit = a.append(n)
  }

  //scalastyle:off cyclomatic.complexity method.length magic.number
  private def h(node: FirrtlNode)(implicit m: MessageDigest, mods: Mods): Unit = node match {
    case NoInfo => // ignore
    case FileInfo(_) => // ignore
    case MultiInfo(_) => // ignore

    // Expressions
    case Reference(name, _, _, _) => id(0) ; h(name)
    case SubField(expr, name, _, _) => id(1) ; h(expr) ; h(name)
    case SubIndex(expr, value, _, _) => id(2) ; h(expr) ; h(value)
    case SubAccess(expr, index, _, _) => id(3) ; h(expr) ; h(index)
    case Mux(cond, tval, fval, _) => id(4) ; h(cond) ; h(tval) ; h(fval)
    case ValidIf(cond, value, _) => id(5) ; h(cond) ; h(value)
    case UIntLiteral(value, width) => id(6) ; h(value) ; h(width)
    case SIntLiteral(value, width) => id(7) ; h(value) ; h(width)
    case FixedLiteral(value, width, point) => id(8) ; h(value) ; h(width) ; h(point)
    case DoPrim(op, args, consts, _) => id(9) ; m.update(primOp(op)) ; args.foreach(h) ; consts.foreach(h)

    // Statements
    case DefWire(_, name, tpe) => id(20) ; h(name) ; h(tpe)
    case DefRegister(info, name, tpe, clock, reset, init) =>
      id(21) ; h(name) ; h(tpe) ; h(clock) ; h(reset) ; h(init)
    case DefInstance(info, name, module, _) => id(22) ; h(name) ; h(module) ; mods.add(module)
    case DefMemory(info, name, dataType, depth, writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite) =>
      id(23) ; h(name) ; h(dataType) ; h(depth) ; h(writeLatency) ; h(readLatency)
      h(readers.length) ; readers.foreach(h)
      h(writers.length) ; writers.foreach(h)
      h(readwriters.length) ; readwriters.foreach(h)
      h(readUnderWrite.toString)
    case DefNode(info, name, value) => id(24) ; h(name) ; h(value)
    case Conditionally(info, pred, conseq, alt) =>
      id(25) ; h(pred) ; h(conseq) ; h(alt)
    case Block(stmts) => id(28) ; h(stmts.length) ; stmts.foreach(h)
    case PartialConnect(info, loc, expr) => id(29) ; h(loc) ; h(expr)
    case Connect(info, loc, expr) => id(30) ; h(loc) ; h(expr)
    case IsInvalid(info, expr) => id(31) ; h(expr)
    case Attach(info, exprs) => id(32) ; h(exprs.length) ; exprs.foreach(h)
    case Stop(info, ret, clk, en) => id(33) ; h(ret) ; h(clk) ; h(en)
    case Print(info, string, args, clk, en) =>
      id(34) ; h(string.string) ; h(args.length) ; args.foreach(h) ; h(clk) ; h(en)
    case EmptyStmt => id(35)

    case IntWidth(width) => id(40) ; h(width)
    case UnknownWidth => id(41)
    case CalcWidth(arg) => id(42) ; h(arg.serialize) // TODO: hash constraints
    case VarWidth(name) => id(43) ; h(name)
    case Default => id(44)
    case Flip => id(45)
    case Field(name, flip, tpe) => id(46) ; h(flip) ; h(tpe)

    // Types
    case UIntType(width) => id(50) ; h(width)
    case SIntType(width) => id(51) ; h(width)
    case FixedType(width, point) => id(52) ; h(width) ; h(point)
    // TODO: hash constraints
    case IntervalType(lower, upper, point) => id(53) ; h(lower.serialize) ; h(upper.serialize) ; h(point)
    case BundleType(fields) => id(54) ; h(fields.length) ; fields.foreach(h)
    case VectorType(tpe, size) => id(55) ; h(tpe) ; h(size)
    case ClockType => id(56)
    case ResetType => id(57)
    case AsyncResetType => id(58)
    case AnalogType(width) => id(59) ; h(width)
    case UnknownType => id(60)

    case Input => id(70)
    case Output => id(71)
    case Port(info, name, direction, tpe) => id(72) ; h(name) ; h(direction) ; h(tpe)
    case IntParam(name, value) => id(73) ; h(name) ; h(value)
    case DoubleParam(name, value) => id(74) ; h(name) ; h(value)
    case StringParam(name, value) => id(75) ; h(name) ; h(value.string)
    case RawStringParam(name, value) => id(76) ; h(name) ; h(value)

    case Module(info, name, ports, body) => id(80) ; h(name) ; h(ports.length) ; ports.foreach(h) ; h(body)
    case ExtModule(info, name, ports, defname, params) =>
      id(81) ; h(name) ; h(ports.length) ; ports.foreach(h) ; h(defname) ; h(params.length) ; params.foreach(h)
    case Circuit(info, modules, main) => id(82) ; h(modules.length) ; modules.foreach(h) ; h(main)

    // WIR
    case firrtl.WVoid => id(100)
    case firrtl.WInvalid => id(101)
    case firrtl.EmptyExpression => id(102)
    case firrtl.CDefMemory(info, name, tpe, size, seq, readUnderWrite) =>
      id(103) ; h(name) ; h(tpe) ; h(size) ; h(seq) ; h(readUnderWrite.toString)
    case firrtl.CDefMPort(info, name, _, mem, exps, direction) =>
      id(104) ; h(name) ; h(mem) ; h(exps.length) ; exps.foreach(h) ; h(direction)

    // Description
    case DocString(string) => id(-60) ; h(string.string)
    case EmptyDescription => id(-61)
    case DescribedStmt(description, stmt) => id(-63) ; h(description) ; h(stmt)

    // MPort
    case MInfer => id(-70)
    case MRead => id(-71)
    case MWrite => id(-72)
    case MReadWrite => id(-73)

    // Emitter
    case VRandom(width) => id(-75) ; h(width)

    // MemIR
    case DefAnnotatedMemory(_, name, dataType, depth, writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite, maskGran, memRef) =>
      id(-77) ; h(name) ; h(dataType) ; h(depth) ; h(writeLatency) ; h(readLatency)
      h(readers.length) ; readers.foreach(h)
      h(writers.length) ; writers.foreach(h)
      h(readwriters.length) ; readwriters.foreach(h)
      h(readUnderWrite.toString)
      h(maskGran.size) ; maskGran.foreach(h)
      h(memRef.size) ; memRef.foreach{ case (a, b) => h(a) ; h(b) }

    case other => h(other.serialize)

    // primops have negative ids -1 .. -50, see primOp method below
  }

  private def primOp(p: PrimOp): Byte = p match {
    case PrimOps.Add => -1
    case PrimOps.Sub => -2
    case PrimOps.Mul => -3
    case PrimOps.Div => -4
    case PrimOps.Rem => -5
    case PrimOps.Lt => -6
    case PrimOps.Leq => -7
    case PrimOps.Gt => -8
    case PrimOps.Geq => -9
    case PrimOps.Eq => -10
    case PrimOps.Neq => -11
    case PrimOps.Pad => -12
    case PrimOps.Shl => -13
    case PrimOps.Shr => -14
    case PrimOps.Dshl => -15
    case PrimOps.Dshr => -16
    case PrimOps.Cvt => -17
    case PrimOps.Neg => -18
    case PrimOps.Not => -19
    case PrimOps.And => -20
    case PrimOps.Or => -21
    case PrimOps.Xor => -22
    case PrimOps.Andr => -23
    case PrimOps.Orr => -24
    case PrimOps.Xorr => -25
    case PrimOps.Cat => -26
    case PrimOps.Bits => -27
    case PrimOps.Head => -28
    case PrimOps.Tail => -29
    case PrimOps.IncP => -30
    case PrimOps.DecP => -31
    case PrimOps.SetP => -32
    case PrimOps.AsUInt => -33
    case PrimOps.AsSInt => -34
    case PrimOps.AsClock => -35
    case PrimOps.AsAsyncReset => -36
    case PrimOps.AsFixedPoint => -37
    case PrimOps.AsInterval => -38
    case PrimOps.Squeeze => -39
    case PrimOps.Wrap => -40
    case PrimOps.Clip => -41
  }
}
