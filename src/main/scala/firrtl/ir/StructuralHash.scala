// See LICENSE for license details.

package firrtl.ir
import firrtl.PrimOps

import java.security.MessageDigest
import scala.collection.mutable

/**
  * This object can performs a "structural" hash over any FirrtlNode.
  * It ignore:
  * - `Expression` types
  * - Any `Info` fields
  * - Description on DescribedStmt
  * - each identifier name is replaced by a unique integer which only depends on the oder of declaration
  *   and is thus deterministic
  *
  * Please note that module hashes don't include any submodules.
  * Two structurally equivalent modules are only functionally equivalent if they are part
  * of the same circuit and thus all modules referred to in DefInstance are the same.
  *
  * @author Kevin Laeufer <laeufer@cs.berkeley.edu>
  * */
object StructuralHash {
  def md5(node: FirrtlNode): MDHashCode = {
    val m = MessageDigest.getInstance("MD5")
    hash(node, MessageDigestHasher(m))
    MDHashCode(m.digest())
  }

  def md5(str: String): MDHashCode = {
    val m = MessageDigest.getInstance("MD5")
    m.update(str.getBytes())
    MDHashCode(m.digest())
  }

  def md5WithPortNames(module: DefModule): MDHashCode = {
    val m = MessageDigest.getInstance("MD5")
    hashModuleAndPortNames(module, MessageDigestHasher(m))
    MDHashCode(m.digest())
  }

  //scalastyle:off cyclomatic.complexity
  private def hash(node: FirrtlNode, h: Hasher): Unit = node match {
    case n : Expression => new StructuralHash(h).hash(n)
    case n : Statement => new StructuralHash(h).hash(n)
    case n : Type => new StructuralHash(h).hash(n)
    case n : Width => new StructuralHash(h).hash(n)
    case n : Orientation => new StructuralHash(h).hash(n)
    case n : Field => new StructuralHash(h).hash(n)
    case n : Direction => new StructuralHash(h).hash(n)
    case n : Port => new StructuralHash(h).hash(n)
    case n : Param => new StructuralHash(h).hash(n)
    case _ : Info => throw new RuntimeException("The structural hash of Info is meaningless.")
    case n : DefModule => new StructuralHash(h).hash(n)
    case n : Circuit => hashCircuit(n, h)
    case n : StringLit => h.update(n.toString)
  }
  //scalastyle:on cyclomatic.complexity

  private def hashModuleAndPortNames(m: DefModule, h: Hasher): Unit = {
    val sh = new StructuralHash(h)
    sh.hash(m)
    sh.hashPortNames()
  }

  private def hashCircuit(c: Circuit, h: Hasher): Unit = {
    h.update(127)
    h.update(c.main)
    // sort modules to make hash more useful
    val mods = c.modules.sortBy(_.name)
    // we create a new StructuralHash for each module since each module has its own namespace
    mods.foreach { m =>
      new StructuralHash(h).hash(m)
    }
  }

  //scalastyle:off cyclomatic.complexity method.length magic.number
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
  //scalastyle:on cyclomatic.complexity method.length magic.number
}

trait HashCode {
  //scalastyle:off method.name
  def ==(other: HashCode): Boolean
  def !=(other: HashCode): Boolean = !(this == other)
  //scalastyle:on method.name
}

case class MDHashCode(code: Array[Byte]) extends HashCode {
  //scalastyle:off method.name
  override def ==(other: HashCode): Boolean = other match {
    case MDHashCode(otherCode) =>
      if(code.length == otherCode.length) {
        code.zip(otherCode).forall(p => p._1 == p._2)
      } else { false }
    case _ => false
  }
  //scalastyle:on method.name
}

/** Generic hashing interface which allows us to use different backends to trade of speed and collision resistance */
private trait Hasher {
  def update(b: Byte): Unit
  def update(i: Int): Unit
  def update(l: Long): Unit
  def update(s: String): Unit
  def update(b: Array[Byte]): Unit
  def update(d: Double): Unit = update(java.lang.Double.doubleToRawLongBits(d))
  def update(i: BigInt): Unit = update(i.toByteArray)
  def update(b: Boolean): Unit = if(b) update(1.toByte) else update(0.toByte)
  def update(i: BigDecimal): Unit = {
    // this might be broken, tried to borrow some code from BigDecimal.computeHashCode
    val temp = i.bigDecimal.stripTrailingZeros()
    val bigInt = temp.scaleByPowerOfTen(temp.scale).toBigInteger
    update(bigInt)
    update(temp.scale)
  }
}

private case class MessageDigestHasher(m: MessageDigest) extends Hasher {
  override def update(b: Byte): Unit = m.update(b)
  override def update(i: Int): Unit = {
    m.update(((i >>  0) & 0xff).toByte)
    m.update(((i >>  8) & 0xff).toByte)
    m.update(((i >> 16) & 0xff).toByte)
    m.update(((i >> 24) & 0xff).toByte)
  }
  override def update(l: Long): Unit = {
    m.update(((l >>  0) & 0xff).toByte)
    m.update(((l >>  8) & 0xff).toByte)
    m.update(((l >> 16) & 0xff).toByte)
    m.update(((l >> 24) & 0xff).toByte)
    m.update(((l >> 32) & 0xff).toByte)
    m.update(((l >> 40) & 0xff).toByte)
    m.update(((l >> 48) & 0xff).toByte)
    m.update(((l >> 56) & 0xff).toByte)
  }
  // the encoding of the bytes should not matter as long as we are on the same platform
  override def update(s: String): Unit = m.update(s.getBytes())
  override def update(b: Array[Byte]): Unit = m.update(b)
}

class StructuralHash private(h: Hasher) {
  // used to track the port names so that they can optionally be hashed
  private val portNames = mutable.ArrayBuffer[String]()
  private def hashPortNames(): Unit = portNames.foreach(hash)
  // replace identifiers with incrementing integers
  private val nameToInt = mutable.HashMap[String, Int]()
  private var nameCounter: Int = 0
  @inline private def n(name: String): Unit = hash(nameToInt.getOrElseUpdate(name, {
    val ii = nameCounter
    nameCounter = nameCounter + 1
    ii
  }))

  // internal convenience methods
  @inline private def id(b: Byte): Unit = h.update(b)
  @inline private def hash(i: Int): Unit = h.update(i)
  @inline private def hash(b: Boolean): Unit = h.update(b)
  @inline private def hash(d: Double): Unit = h.update(d)
  @inline private def hash(i: BigInt): Unit = h.update(i)
  @inline private def hash(i: BigDecimal): Unit = h.update(i)
  @inline private def hash(s: String): Unit = h.update(s)

  //scalastyle:off magic.number
  //scalastyle:off cyclomatic.complexity
  private def hash(node: Expression): Unit = node match {
    case Reference(name, _, _, _) => id(0) ; n(name)
    case DoPrim(op, args, consts, _) =>
      // no need to hash the number of arguments or constants since that is implied by the op
      id(1) ; h.update(StructuralHash.primOp(op)) ; args.foreach(hash) ; consts.foreach(hash)
    case UIntLiteral(value, width) => id(2) ; hash(value) ; hash(width)
    case SubField(expr, name, _, _) => id(3) ; hash(expr) ;  n(name)
    case SubIndex(expr, value, _, _) => id(4) ; hash(expr) ; hash(value)
    case SubAccess(expr, index, _, _) => id(5) ; hash(expr) ; hash(index)
    case Mux(cond, tval, fval, _) => id(6) ; hash(cond) ; hash(tval) ; hash(fval)
    case ValidIf(cond, value, _) => id(7) ; hash(cond) ; hash(value)
    case SIntLiteral(value, width) => id(8) ; hash(value) ; hash(width)
    case FixedLiteral(value, width, point) => id(9) ; hash(value) ; hash(width) ; hash(point)
    // WIR
    case firrtl.WVoid => id(10)
    case firrtl.WInvalid => id(11)
    case firrtl.EmptyExpression => id(12)
    // VRandom is used in the Emitter
    case firrtl.VRandom(width) => id(13) ;  hash(width)
    // ids 14 ... 19 are reserved for future Expression nodes
  }
  //scalastyle:on cyclomatic.complexity

  //scalastyle:off cyclomatic.complexity method.length
  private def hash(node: Statement): Unit = node match {
    // all info fields are ignore
    case DefNode(_, name, value) => id(20) ; n(name) ; hash(value)
    case Connect(_, loc, expr) => id(21) ; hash(loc) ; hash(expr)
    case Conditionally(_, pred, conseq, alt) => id(22) ; hash(pred) ; hash(conseq) ; hash(alt)
    case EmptyStmt => id(23)
    case Block(stmts) => id(24) ; hash(stmts.length) ; stmts.foreach(hash)
    case Stop(_, ret, clk, en) => id(25) ; hash(ret) ; hash(clk) ; hash(en)
    case Print(_, string, args, clk, en) =>
      // the string is part of the side effect and thus part of the circuit behavior
      id(26) ; hash(string.string) ; hash(args.length) ; args.foreach(hash) ; hash(clk) ; hash(en)
    case IsInvalid(_, expr) => id(27) ; hash(expr)
    case DefWire(_, name, tpe) => id(28) ; n(name) ; hash(tpe)
    case DefRegister(_, name, tpe, clock, reset, init) =>
      id(29) ; n(name) ; hash(tpe) ; hash(clock) ; hash(reset) ; hash(init)
    case DefInstance(_, name, module, _) =>
      // module is in the global namespace which is why we cannot replace it with a numeric id
      id(30) ; n(name) ; hash(module)
    // descriptions on statements are ignores
    case firrtl.DescribedStmt(_, stmt) => hash(stmt)
    case DefMemory(_, name, dataType, depth, writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite) =>
      id(30) ; n(name) ;  hash(dataType) ;  hash(depth) ;  hash(writeLatency) ;  hash(readLatency)
      hash(readers.length) ; readers.foreach(hash)
      hash(writers.length) ; writers.foreach(hash)
      hash(readwriters.length) ; readwriters.foreach(hash)
      hash(readUnderWrite)
    case PartialConnect(_, loc, expr) => id(31) ; hash(loc) ; hash(expr)
    case Attach(_, exprs) => id(32) ; hash(exprs.length) ; exprs.foreach(hash)
    // WIR
    case firrtl.CDefMemory(_, name, tpe, size, seq, readUnderWrite) =>
      id(33) ; n(name) ; hash(tpe); hash(size) ; hash(seq) ; hash(readUnderWrite)
    case firrtl.CDefMPort(_, name, _, mem, exps, direction) =>
      // the type of the MPort depends only on the memory (in well types firrtl) and can thus be ignored
      id(34) ; n(name) ; n(mem) ; hash(exps.length) ; exps.foreach(hash) ; hash(direction)
    // DefAnnotatedMemory from MemIR.scala
    case firrtl.passes.memlib.DefAnnotatedMemory(_, name, dataType, depth, writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite, maskGran, memRef) =>
      id(35) ;  n(name) ;  hash(dataType) ;  hash(depth) ;  hash(writeLatency) ;  hash(readLatency)
      hash(readers.length) ; readers.foreach(hash)
      hash(writers.length) ; writers.foreach(hash)
      hash(readwriters.length) ; readwriters.foreach(hash)
      hash(readUnderWrite.toString)
      hash(maskGran.size) ; maskGran.foreach(hash)
      hash(memRef.size) ; memRef.foreach{ case (a, b) =>  hash(a) ;  hash(b) }
    // ids 36 ... 39 are reserved for future Statement nodes
  }
  //scalastyle:on cyclomatic.complexity method.length

  // ReadUnderWrite is never used in place of a FirrtlNode and thus we can start a new id namespace
  private def hash(ruw: ReadUnderWrite.Value): Unit = ruw match {
    case ReadUnderWrite.New => id(0)
    case ReadUnderWrite.Old => id(1)
    case ReadUnderWrite.Undefined => id(2)
  }

  private def hash(node: Width): Unit = node match {
    case IntWidth(width) => id(40) ; hash(width)
    case UnknownWidth => id(41)
    case CalcWidth(arg) => id(42) ; hash(arg)
    case VarWidth(name) => id(43) ; n(name)
    // ids 44 + 45 are reserved for future Width nodes
  }

  private def hash(node: Orientation): Unit = node match {
    case Default => id(46)
    case Flip => id(47)
  }

  private def hash(node: Field): Unit = {
    // TODO: is it correct ot use n(..) here?
    id(48) ; n(node.name) ; hash(node.flip) ; hash(node.tpe)
  }

  //scalastyle:off cyclomatic.complexity
  private def hash(node: Type): Unit = node match {
    // Types
    case UIntType(width: Width) => id(50) ; hash(width)
    case SIntType(width: Width) => id(51) ; hash(width)
    case FixedType(width, point) => id(52) ; hash(width) ; hash(point)
    case BundleType(fields) => id(53) ; hash(fields.length) ; fields.foreach(hash)
    case VectorType(tpe, size) => id(54) ; hash(tpe) ; hash(size)
    case ClockType => id(55)
    case ResetType => id(56)
    case AsyncResetType => id(57)
    case AnalogType(width) => id(58) ; hash(width)
    case UnknownType => id(59)
    case IntervalType(lower, upper, point) => id(60) ; hash(lower) ;  hash(upper) ;  hash(point)
    // ids 61 ... 65 are reserved for future Type nodes
  }
  //scalastyle:on cyclomatic.complexity

  private def hash(node: Direction): Unit = node match {
    case Input => id(66)
    case Output => id(67)
  }

  private def hash(node: Port): Unit = {
    portNames.append(node.name)
    id(68) ; n(node.name) ; hash(node.direction) ; hash(node.tpe)
  }

  private def hash(node: Param): Unit = node match {
    case IntParam(name, value) => id(70) ; n(name) ; hash(value)
    case DoubleParam(name, value) => id(71) ; n(name) ; hash(value)
    case StringParam(name, value) => id(72) ; n(name) ; hash(value.string)
    case RawStringParam(name, value) => id(73) ; n(name) ; hash(value)
    // id 74 is reserved for future use
  }

  private def hash(node: DefModule): Unit = node match {
    case Module(_, name, ports, body) =>
      id(75) ; n(name) ; hash(ports.length) ; ports.foreach(hash) ; hash(body)
    case ExtModule(_, name, ports, defname, params) =>
      id(76) ; hash(name) ; hash(ports.length) ; ports.foreach(hash) ; hash(defname)
      hash(params.length) ; params.foreach(hash)
  }

  // id 127 is reserved for Circuit nodes

  private def hash(d: firrtl.MPortDir): Unit = d match {
    case firrtl.MInfer => id(-70)
    case firrtl.MRead => id(-71)
    case firrtl.MWrite => id(-72)
    case firrtl.MReadWrite => id(-73)
  }

  private def hash(c: firrtl.constraint.Constraint): Unit = c match {
    case b: Bound => hash(b) /* uses ids -80 ... -84 */
    case firrtl.constraint.IsAdd(known, maxs, mins, others) =>
      id(-85) ; hash(known.nonEmpty) ; known.foreach(hash)
      hash(maxs.length) ; maxs.foreach(hash)
      hash(mins.length) ; mins.foreach(hash)
      hash(others.length) ; others.foreach(hash)
    case firrtl.constraint.IsFloor(child, dummyArg) => id(-86) ; hash(child) ; hash(dummyArg)
    case firrtl.constraint.IsKnown(decimal) => id(-87) ; hash(decimal)
    case firrtl.constraint.IsNeg(child, dummyArg) => id(-88) ; hash(child) ; hash(dummyArg)
    case firrtl.constraint.IsPow(child, dummyArg) => id(-89) ; hash(child) ; hash(dummyArg)
    case firrtl.constraint.IsVar(str) => id(-90) ; n(str)
  }

  private def hash(b: Bound): Unit = b match {
    case UnknownBound => id(-80)
    case CalcBound(arg) => id(-81) ; hash(arg)
    case VarBound(name) => id(-82) ; n(name)
    case Open(value) => id(-83) ; hash(value)
    case Closed(value) => id(-84) ; hash(value)
  }
}