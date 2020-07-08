// See LICENSE for license details.

package firrtlTests.passes

import firrtl.ir.SubField
import firrtl.options.Dependency
import firrtl.stage.TransformManager
import firrtl.{CircuitState, InstanceKind, NodeKind, PortKind, RegKind, SinkFlow, SourceFlow, WireKind, ir, passes}
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
  private def getModule(c: ir.Circuit, name: String): ir.Module =
    c.modules.find(_.name == name).get.asInstanceOf[ir.Module]

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
    val m = getModule(infer(
      """circuit m:
        |  module other:
        |    output x: { y: UInt, flip z: UInt<1> }
        |  module m:
        |    inst i of other
        |    node i_x = i.x
        |    node i_x_y = i.x.y
        |    node i_x_y_2 = i_x.y
        |    node a = UInt<1>(1)
        |    i.x.z <= a
        |""".stripMargin), "m")
    val node = getNodes(m.body).toMap
    val con = getConnects(m.body)


    // node i_x_y = i.x.y
    assert(node("i_x_y").tpe.isInstanceOf[ir.UIntType])
    // the type inference replaces all unknown widths with a variable
    assert(node("i_x_y").tpe.asInstanceOf[ir.UIntType].width.isInstanceOf[ir.VarWidth])
    assert(node("i_x_y").asInstanceOf[ir.SubField].flow == SourceFlow)


    // node i_x = i.x
    val x = node("i_x_").asInstanceOf[ir.SubField]
    assert(x.tpe.isInstanceOf[ir.BundleType])
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.head.name == "y")
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.head.tpe == node("i_x_y").tpe)
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.head.flip == ir.Default)
    assert(x.tpe.asInstanceOf[ir.BundleType].fields.last.flip == ir.Flip)
    assert(x.flow == SourceFlow)

    val i = x.expr.asInstanceOf[ir.Reference]
    assert(i.kind == InstanceKind)
    assert(i.flow == SourceFlow)


    // node i_x_y_2 = i_x.y
    assert(node("i_x_y").tpe == node("i_x_y_2").tpe)
    assert(node("i_x_y").asInstanceOf[ir.SubField].flow == node("i_x_y_2").asInstanceOf[ir.SubField].flow)


    // i.x.z <= a
    val (left, right) = (con.head.loc.asInstanceOf[ir.SubField], con.head.expr.asInstanceOf[ir.Reference])

    // flow propagates z -> x -> i
    assert(left.flow == SinkFlow)
    val left_x = left.expr.asInstanceOf[SubField]
    assert(left_x.flow == SourceFlow) // flip z
    val left_i = left_x.expr.asInstanceOf[ir.Reference]
    assert(left_i.flow == SourceFlow)

    assert(left_i.kind == InstanceKind)
    assert(left_x.tpe == x.tpe)
  }

  it should "infer types for references to memories" in {



  }

  it should "infer different instances of the same module to have the same width variable" in {
    val c = infer(
      """circuit m:
        |  module other:
        |    input x: UInt
        |  module x:
        |    inst i of other
        |    i.x <= UInt<16>(3)
        |  module m:
        |    inst x of x
        |    inst i of other
        |    i.x <= UInt<1>(1)
        |""".stripMargin)
    val m_con = getConnects(getModule(c, "m").body).head
    val x_con = getConnects(getModule(c, "x").body).head
    val other = getModule(c, "other")

    // this is the type of the other.x port
    val tpe = m_con.loc.tpe.asInstanceOf[ir.UIntType]
    assert(tpe.width.isInstanceOf[ir.VarWidth])
    // since it is the only unknown width, it should just be replaced with a "w"
    assert(tpe.width.asInstanceOf[ir.VarWidth].name == "w")

    assert(m_con.loc.tpe == tpe)
    assert(x_con.loc.tpe == tpe)
    assert(other.ports.head.tpe == tpe)
  }

}
