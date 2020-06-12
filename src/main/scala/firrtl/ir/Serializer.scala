// See LICENSE for license details.

package firrtl.ir

import firrtl.constraint.Constraint

object Serializer {
  val NewLine = '\n'
  val Indent = "  "

  def serialize(node: FirrtlNode): String = {
    val builder = new StringBuilder()
    val indent = 0
    s(node)(builder, indent)
    builder.toString()
  }

  private def flattenInfo(infos: Seq[Info]): Seq[FileInfo] = infos.flatMap {
    case NoInfo => Seq()
    case f : FileInfo => Seq(f)
    case MultiInfo(infos) => flattenInfo(infos)
  }

  //scalastyle:off cyclomatic.complexity method.length
  private def s(node: FirrtlNode)(implicit b: StringBuilder, indent: Int): Unit = node match {
    case NoInfo => // empty string
    case FileInfo(info) => b ++= " @[" ; s(info) ; b ++= "]"
    case MultiInfo(infos) => throw new NotImplementedError()
    case s : StringLit =>
      if(s.string.contains(']')) { // s.string.contains('\n') || s.string.contains('\r') ||
        b ++= s.serialize
      } else {
        b ++= s.string
      }

    // Expressions
    case Reference(name, _, _, _) => b ++= name
    // TODO: benchmark `builder ++= "." ; builder ++= name` vs `builder ++= "." + name`
    case SubField(expr, name, _, _) => s(expr) ; b += '.' ; b ++= name
    case SubIndex(expr, value, _, _) => s(expr) ; b += '[' ; b ++= value.toString ; b += ']'
    case SubAccess(expr, index, _, _) => s(expr) ; b += '[' ; s(index) ; b += ']'
    case Mux(cond, tval, fval, _) =>
      b ++= "mux(" ; s(cond) ; b ++= ", " ; s(tval) ; b ++= ", " ; s(fval) ; b += ')'
    case ValidIf(cond, value, _) => b ++= "validif(" ; s(cond) ; b ++= ", " ; s(value) ; b += ')'
    case UIntLiteral(value, width) =>
      b ++= "UInt" ; s(width) ; b ++= "(\"h" ; b ++= value.toString(16) ; b ++= "\")"
    case SIntLiteral(value, width) =>
      b ++= "SInt" ; s(width) ; b ++= "(\"h" ; b ++= value.toString(16) ; b ++= "\")"
    case FixedLiteral(value, width, point) =>
      // TODO: old serialization code puts "<" and ">" around the width,
      //  but this should be handled by the width serialization...
      b ++= "Fixed" ; s(width) ; s(point) ; b ++= "(\"h" ; b ++= value.toString(16) ; b ++= "\")"
    case DoPrim(op, args, consts, _) =>
      b ++= op.toString ; b += '(' ; s(args, ", ", consts.isEmpty) ; s(consts, ", ") ; b += ')'

    // Statements
    case DefWire(info, name, tpe) => b ++= "wire " ; b ++= name ; b ++= " : " ; s(tpe) ; s(info)
    case DefRegister(info, name, tpe, clock, reset, init) =>
      // TODO: init is missing!
      b ++= "reg " ; b ++= name ; b ++= " : " ; s(tpe) ; b ++= ", " ; s(clock) ; b ++= " with :" ; newLineAndIndent(1)
      b ++= "reset => (" ; s(reset) ; b ++= ", " ; b += ')' ; s(info)
    case DefInstance(info, name, module, _) => b ++= "inst " ; b ++= name ; b ++= " of " ; b ++= module ; s(info)
    case DefMemory(info, name, dataType, depth, writeLatency, readLatency, readers, writers,
                   readwriters, readUnderWrite) =>
      b ++= "mem " ; b ++= name ; b ++= " :" ; s(info) ; newLineAndIndent(1)
      b ++= "data-type => "     ; s(dataType) ; newLineAndIndent(1)
      b ++= "depth => "         ; b ++= depth.toString() ; newLineAndIndent(1)
      b ++= "read-latency => "  ; b ++= readLatency.toString ; newLineAndIndent(1)
      b ++= "write-latency => " ; b ++= writeLatency.toString ; newLineAndIndent(1)
      readers.foreach{ r => b ++= "reader => " ; b ++= r ; newLineAndIndent(1) }
      writers.foreach{ w => b ++= "writer => " ; b ++= w ; newLineAndIndent(1) }
      readwriters.foreach{ r => b ++= "readwriter => " ; b ++= r ; newLineAndIndent(1) }
      b ++= "read-under-write => " ; b ++= readUnderWrite.toString
    case DefNode(info, name, value) => b ++= "node " ; b ++= name ; b ++= " = " ; s(value) ; s(info)
    case Conditionally(info, pred, conseq, alt) =>
      b ++= "when " ; s(pred) ; b ++= " :" ; s(info)
      newLineAndIndent(1) ; s(conseq)(b, indent + 1)
      if(alt != EmptyStmt) {
        newLineAndIndent() ; b ++= "else :"
        newLineAndIndent(1) ; s(alt)(b, indent + 1)
      }
    case Block(stmts) =>
      val it = stmts.iterator
      while(it.hasNext) {
        s(it.next)
        if(it.hasNext) newLineAndIndent()
      }
    case PartialConnect(info, loc, expr) => s(loc) ; b ++= " <- " ; s(expr) ; s(info)
    case Connect(info, loc, expr) => s(loc) ; b ++= " <= " ; s(expr) ; s(info)
    case IsInvalid(info, expr) => s(expr) ; b ++= " is invalid" ; s(info)
    case Attach(info, exprs) =>
      b ++= "attach "
      if(exprs.nonEmpty) { // TODO: can exprs ever be empty?
        b += '(' ; s(exprs, ", ") ; b += ')'
      }
      // TODO: what about info?
      s(info)
    case Stop(info, ret, clk, en) =>
      b ++= "stop(" ; s(clk) ; b ++= ", " ; s(en) ; b ++= ", " ; b ++= ret.toString ; b += ')' ; s(info)
    case Print(info, string, args, clk, en) =>
      b ++= "printf(" ; s(clk) ; b ++= ", " ; s(en) ; b ++= ", " ; b ++= string.escape ; b += ')' ; s(info)
    case EmptyStmt => b ++= "skip"

    case IntWidth(width) => b += '<' ; b ++= width.toString() ; b += '>'
    case UnknownWidth => // empty string
    case CalcWidth(arg) => b ++= "calcw(" ; s(arg) ; b += ')'
    case VarWidth(name) => b += '<' ; b ++= name ; b += '>'
    case Default => // empty string
    case Flip => b ++= "flip"
    case Field(name, flip, tpe) => s(flip) ; b ++= name ; b ++= " : " ; s(tpe)

    // Types
    case UIntType(width: Width) => b ++= "UInt" ; s(width)
    case SIntType(width: Width) => b ++= "SInt" ; s(width)
    case FixedType(width, point) => b ++= "Fixed" ; s(width) ; s(point)
    // TODO: case IntervalType
    case BundleType(fields) => b ++= "{ " ; s(fields, ", ") ; b += '}'
    case VectorType(tpe, size) => s(tpe) ; b += '[' ; b ++= size.toString ; b += ']'
    case ClockType => b ++= "Clock"
    case ResetType => b ++= "Reset"
    case AsyncResetType => b ++= "AsyncReset"
    case AnalogType(width) => b ++= "Analog" ; s(width)
    case UnknownType => b += '?'

    case Input => b ++= "input"
    case Output => b ++= "output"
    case Port(info, name, direction, tpe) =>
      s(direction) ; b += ' ' ; b ++= name ; b ++= " : " ; s(tpe) ; s(info)
    case IntParam(name, value) => b ++= "parameter " ; b ++= name ; b ++= " = " ; b ++= value.toString
    case DoubleParam(name, value) => b ++= "parameter " ; b ++= name ; b ++= " = " ; b ++= value.toString
    case StringParam(name, value) => b ++= "parameter " ; b ++= name ; b ++= " = " ; b ++= value.escape
    case RawStringParam(name, value) =>
      b ++= "parameter " ; b ++= name ; b ++= " = "
      b += '\'' ; b ++= value.replace("'", "\\'") ; b += '\''

    case Module(info, name, ports, body) =>
      b ++= "module " ; b ++= name ; b ++= " :" ; s(info)
      ports.foreach{ p => newLineAndIndent(1) ;  s(p) }
      newLineAndIndent(2) ; s(body)(b, indent + 2)
    case ExtModule(info, name, ports, defname, params) =>
      b ++= "extmodule " ; b ++= name ; b ++= " :" ; s(info) ; newLineAndIndent(1)
      ports.foreach{ p => newLineAndIndent(1) ; s(p) }
      newLineAndIndent(1)  ; b ++= "defname = " ; b ++= defname
      params.foreach{ p => newLineAndIndent(1) ; s(p) }
    case Circuit(info, modules, main) =>
      b ++= "circuit " ; b ++= main ; b ++= " :" ; s(info)
      modules.foreach{m => newLineAndIndent(1) ; s(m)(b, indent + 1) }

    // WIR
    case firrtl.WVoid => b ++= "VOID"
    case firrtl.WInvalid => b ++= "INVALID"
    case firrtl.EmptyExpression => b ++= "EMPTY"
    case firrtl.CDefMemory(info, name, tpe, size, seq, readUnderWrite) =>
      if(seq) b ++= "smem " else b ++= "cmem "
      b ++= name ; b ++= " : " ; s(tpe) ; b ++= " [" ; b ++= size.toString() ; b += ']' ; s(info)
    case firrtl.CDefMPort(info, name, _, mem, exps, direction) =>
      b ++= direction.serialize ; b ++= " mport " ; b ++= name ; b ++= " = " ; b ++= mem
      b += '[' ; s(exps.head) ; b ++= "], " ; s(exps(1)) ; s(info)

    // case other => b ++= other.serialize
  }

  // serialize constraints
  private def s(const: Constraint)(implicit b: StringBuilder): Unit = const match {
    // Bounds
    case UnknownBound => b += '?'
    case CalcBound(arg) => b ++= "calcb(" ; s(arg) ; b += ')'
  }

  /** create a new line with the appropriate indent */
  private def newLineAndIndent(inc: Int = 0)(implicit b: StringBuilder, indent: Int): Unit = {
    b += NewLine ; doIndent(inc)
  }

  /** create indent, inc allows for a temporary increment */
  private def doIndent(inc: Int = 0)(implicit b: StringBuilder, indent: Int): Unit = {
    (0 until (indent + inc)).foreach(b ++= Indent)
  }


  /** serialize firrtl nodes with a custom separator and the option to include the separator at the end */
  private def s(nodes: Seq[FirrtlNode], sep: String, noFinalSep: Boolean = true)
               (implicit b: StringBuilder, indent: Int): Unit = {
    val it = nodes.iterator
    while(it.hasNext) {
      s(it.next())
      if(!noFinalSep || it.hasNext) b ++= sep
    }
  }

  /** serialize BigInts with a custom separator */
  private def s(consts: Seq[BigInt], sep: String)(implicit b: StringBuilder): Unit = {
    val it = consts.iterator
    while(it.hasNext) {
      b ++= it.next().toString()
      if(it.hasNext) b ++= sep
    }
  }
}
