// See LICENSE for license details.

package firrtl.ir
import firrtl.passes.memlib.DefAnnotatedMemory
import firrtl.{DescribedStmt, DocString, EmptyDescription, MInfer, MRead, MReadWrite, MWrite, VRandom}

import scala.collection.mutable


class NodeCounter {
  def count(node: FirrtlNode): Map[String,Long] = {
    _map.clear()
    c(node)
    _map.toMap
  }

  def countAntPrint(node: FirrtlNode): Unit = {
    val res = count(node).toSeq.sortBy(_._2).reverse
    res.foreach { case (name, cnt) =>
      println(s"$name: $cnt")
    }
  }

  private val _map = new mutable.HashMap[String,Long]() { override def default(key:String): Long = 0 }
  private def c(lbl: String): Unit = _map(lbl) = _map(lbl) + 1

  //scalastyle:off cyclomatic.complexity method.length magic.number
  private def c(node: FirrtlNode): Unit = node match {
    case NoInfo => c("NoInfo")
    case FileInfo(_) => c("FileInfo")
    case m : MultiInfo => c("MultiInfo") // inacurate ...

    // Expressions
    case Reference(name, _, _, _) => c("Reference")
    case SubField(expr, name, _, _) => c("SubField") ; c(expr)
    case SubIndex(expr, value, _, _) => c("SubIndex") ; c(expr)
    case SubAccess(expr, index, _, _) => c("SubAccess") ; c(expr) ; c(index)
    case Mux(cond, tval, fval, _) => c("Mux"); c(cond) ; c(tval) ; c(fval)
    case ValidIf(cond, value, _) => c("ValidIf") ; c(cond) ; c(value)
    case UIntLiteral(value, width) => c("UIntLiteral") ; c(width)
    case SIntLiteral(value, width) => c("SIntLiteral") ; c(width)
    case FixedLiteral(value, width, point) => c("FixedLiteral") ; c(width) ; c(point)
    case DoPrim(op, args, consts, _) => c("DoPrim") ; c(op.serialize) ; args.foreach(c)

    // Statements
    case DefWire(_, name, tpe) => c("DefWire") ; c(tpe)
    case DefRegister(info, name, tpe, clock, reset, init) =>
      c("DefRegister") ; c(tpe) ; c(clock) ; c(reset) ; c(init)
    case DefInstance(info, name, module, _) => c("DefInstance")
    case DefMemory(info, name, dataType, depth, writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite) =>
      c("DefMemory") ; c(dataType)
    case DefNode(info, name, value) => c("DefNode"); c(value)
    case Conditionally(info, pred, conseq, alt) => c("Conditionally") ; c(pred) ; c(conseq) ; c(alt)
    case Block(stmts) => c("Block"); stmts.foreach(c)
    case PartialConnect(info, loc, expr) => c("PartialConnect") ; c(loc) ; c(expr)
    case Connect(info, loc, expr) => c("Connect") ; c(loc) ; c(expr)
    case IsInvalid(info, expr) => c("IsInvalid") ; c(expr)
    case Attach(info, exprs) => c("Attach") ; exprs.foreach(c)
    case Stop(info, ret, clk, en) => c("Stop") ; c(clk) ; c(en)
    case Print(info, string, args, clk, en) => c("Print"); args.foreach(c) ; c(clk) ; c(en)
    case EmptyStmt => c("EmptyStmt")

    case IntWidth(width) => c("IntWidth")
    case UnknownWidth => c("UnknownWidth")
    case CalcWidth(arg) => c("CalcWidth")
    case VarWidth(name) => c("VarWidth")
    case Default => c("Default")
    case Flip => c("Flip")
    case Field(name, flip, tpe) => c("Field") ; c(flip) ; c(tpe)

    // Types
    case UIntType(width) => c("UIntType") ; c(width)
    case SIntType(width) => c("SIntType") ; c(width)
    case FixedType(width, point) => c("FixedType") ; c(width) ; c(point)
    // TODO: hash constraints
    case IntervalType(lower, upper, point) => c("IntervalType") ; c(point)
    case BundleType(fields) => c("BundleType") ; fields.foreach(c)
    case VectorType(tpe, size) => c("VectorType") ; c(tpe)
    case ClockType => c("ClockType")
    case ResetType => c("ResetType")
    case AsyncResetType => c("AsyncResetType")
    case AnalogType(width) => c("AnalogType"); c(width)
    case UnknownType => c("UnknownType")

    case Input => c("Input")
    case Output => c("Output")
    case Port(info, name, direction, tpe) => c("Port") ; c(direction) ; c(tpe)
    case IntParam(name, value) => c("IntParam")
    case DoubleParam(name, value) => c("DoubleParam")
    case StringParam(name, value) => c("StringParam") ; c(value)
    case RawStringParam(name, value) => c("RawStringParam")

    case Module(info, name, ports, body) => c("Module") ; ports.foreach(c) ; c(body)
    case ExtModule(info, name, ports, defname, params) =>
      c("ExtModule") ; ports.foreach(c) ; c(defname); params.foreach(c)
    case Circuit(info, modules, main) => c("Circuit") ; modules.foreach(c) ; c(main)

    // WIR
    case firrtl.WVoid => c("WVoid")
    case firrtl.WInvalid => c("WInvalid")
    case firrtl.EmptyExpression => c("EmptyExpression")
    case firrtl.CDefMemory(info, name, tpe, size, seq, readUnderWrite) =>
      c("CDefMemory") ; c(tpe)
    case firrtl.CDefMPort(info, name, _, mem, exps, direction) =>
      c("CDefMPort") ; exps.foreach(c) ; c(direction)

    // Description
    case DocString(string) => c("DocString")
    case EmptyDescription => c("EmptyDescription")
    case DescribedStmt(description, stmt) => c("DescribedStmt") ; c(stmt)

    // MPort
    case MInfer => c("MInfer")
    case MRead => c("MRead")
    case MWrite => c("MWrite")
    case MReadWrite => c("MReadWrite")

    // Emitter
    case VRandom(width) => c("VRandom")

    // MemIR
    case DefAnnotatedMemory(_, name, dataType, depth, writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite, maskGran, memRef) =>
      c("DefAnnotatedMemory")
      c(dataType)

    case _ : StringLit => c("StringLit")
  }
}
