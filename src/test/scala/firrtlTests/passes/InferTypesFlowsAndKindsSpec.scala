// See LICENSE for license details.

package firrtlTests.passes

import firrtl.options.Dependency
import firrtl.stage.TransformManager
import firrtl.{CircuitState, InstanceKind, NodeKind, PortKind, RegKind, SourceFlow, WireKind, ir, passes}
import org.scalatest._

class InferTypesFlowsAndKindsSpec extends FlatSpec {
  private val deps = Seq(
    Dependency(passes.ResolveKinds),
    Dependency(passes.InferTypes),
    Dependency(passes.ResolveFlows))
  private val manager = new TransformManager(deps)
  private def infer(src: String): ir.Circuit =
    manager.execute(CircuitState(firrtl.Parser.parse(src), Seq())).circuit
  private def getNodes(s: ir.Statement): Seq[(String, ir.Expression)] = s match {
    case ir.DefNode(_, name, value) => Seq((name, value))
    case ir.Block(stmts) => stmts.flatMap(getNodes)
    case ir.Conditionally(_, _, a, b) => Seq(a,b).flatMap(getNodes)
    case _ => Seq()
  }
  private def getConnects(s: ir.Statement): Seq[ir.Connect] = s match {
    case c : ir.Connect => Seq(c)
    case ir.Block(stmts) => stmts.flatMap(getConnects)
    case ir.Conditionally(_, _, a, b) => Seq(a,b).flatMap(getConnects)
    case _ => Seq()
  }

  it should "infer references to ports, wires, nodes and registers" in {
    val node = getNodes(infer(
      """circuit m:
        |  module m:
        |    input clk: Clock
        |    input a: UInt<4>
        |    wire b : SInt<5>
        |    reg c: UInt<5>, clk
        |    node na = a
        |    node nb = b
        |    node nc = c
        |    node nna = na
        |    node na2 = a
        |    node a_plus_c = add(a, c)
        |""".stripMargin).modules.head.asInstanceOf[ir.Module].body).toMap

    assert(node("na").tpe == ir.UIntType(ir.IntWidth(4)))
    assert(node("na").asInstanceOf[ir.Reference].flow == SourceFlow)
    assert(node("na").asInstanceOf[ir.Reference].kind == PortKind)

    assert(node("nb").tpe == ir.SIntType(ir.IntWidth(5)))
    assert(node("nb").asInstanceOf[ir.Reference].flow == SourceFlow)
    assert(node("nb").asInstanceOf[ir.Reference].kind == WireKind)

    assert(node("nc").tpe == ir.UIntType(ir.IntWidth(5)))
    assert(node("nc").asInstanceOf[ir.Reference].flow == SourceFlow)
    assert(node("nc").asInstanceOf[ir.Reference].kind == RegKind)

    assert(node("nna").tpe == ir.UIntType(ir.IntWidth(4)))
    assert(node("nna").asInstanceOf[ir.Reference].flow == SourceFlow)
    assert(node("nna").asInstanceOf[ir.Reference].kind == NodeKind)

    assert(node("na2").tpe == ir.UIntType(ir.IntWidth(4)))
    assert(node("na2").asInstanceOf[ir.Reference].flow == SourceFlow)
    assert(node("na2").asInstanceOf[ir.Reference].kind == PortKind)

    // according to the spec, the result of add is max(we1, we2 ) + 1
    assert(node("a_plus_c").tpe == ir.UIntType(ir.IntWidth(6)))
  }

  it should "infer types for references to instances" in {
    val m = infer(
      """circuit m:
        |  module other:
        |    output x: { y: UInt, flip z: UInt<1> }
        |  module m:
        |    inst i of other
        |    node i_x = i.x
        |    node i_x_y = i.x.y
        |    node a = UInt<1>(1)
        |    i.x.z <= a
        |""".stripMargin).modules.head.asInstanceOf[ir.Module]
    val node = getNodes(m.body).toMap
    val con = getConnects(m.body)

    // TODO: update below

    // node x_y = x.y
    assert(node("x_y").tpe.isInstanceOf[ir.UIntType])
    // the type inference replaces all unknown widths with a variable
    assert(node("x_y").tpe.asInstanceOf[ir.UIntType].width.isInstanceOf[ir.VarWidth])
    assert(node("x_y").asInstanceOf[ir.SubField].flow == SourceFlow)
    val x = node("x_y").asInstanceOf[ir.SubField].expr.asInstanceOf[ir.Reference]
    assert(x.tpe.isInstanceOf[ir.BundleType])
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.head.name == "y")
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.head.tpe == node("x_y").tpe)
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.head.flip == ir.Default)
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.last.flip == ir.Flip)
    assert(x.kind == InstanceKind)
    assert(x.flow == SourceFlow)
    val portXType = x.tpe

    // x.z <= a
    val (left, right) = (con.head.loc.asInstanceOf[ir.SubField], con.head.expr.asInstanceOf[ir.Reference])
    //assert(left == ir.SubField(ir.Reference()))

  }

  it should "infer types for references to memories" in {}

}
