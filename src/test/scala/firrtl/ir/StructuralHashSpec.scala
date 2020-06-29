// See LICENSE for license details.

package firrtl.ir

import firrtl.PrimOps._
import org.scalatest._
import firrtl.{HighFirrtlCompiler}

class StructuralHashSpec extends FlatSpec {
  private def md5(n: FirrtlNode): HashCode = StructuralHash.md5(n, true)
  private val highFirrtlCompiler = new HighFirrtlCompiler
  private def parse(circuit: String): Circuit = {
    val rawFirrtl = firrtl.Parser.parse(circuit)
    // TODO: remove requirement that Firrtl needs to be type checked.
    //       The only reason this is needed for the structural hash right now is because we
    //       define bundles with the same list of field types to be the same, regardless of the
    //       name of these fields. Thus when the fields are accessed, we need to know their position
    //       in order to appropriately hash them.
    highFirrtlCompiler.transform(firrtl.CircuitState(rawFirrtl, Seq())).circuit
  }

  private val b0 = UIntLiteral(0,IntWidth(1))
  private val b1 = UIntLiteral(1,IntWidth(1))
  private val add = DoPrim(Add, Seq(b0, b1), Seq(), UnknownType)

  it should "generate the same hash if the objects are structurally the same" in {
    assert(md5(b0) == md5(UIntLiteral(0,IntWidth(1))))
    assert(md5(b0) != md5(UIntLiteral(1,IntWidth(1))))
    assert(md5(b0) != md5(UIntLiteral(1,IntWidth(2))))

    assert(md5(b1) == md5(UIntLiteral(1,IntWidth(1))))
    assert(md5(b1) != md5(UIntLiteral(0,IntWidth(1))))
    assert(md5(b1) != md5(UIntLiteral(1,IntWidth(2))))
  }

  it should "ignore expression types" in {
    assert(md5(add) == md5(DoPrim(Add, Seq(b0, b1), Seq(), UnknownType)))
    assert(md5(add) == md5(DoPrim(Add, Seq(b0, b1), Seq(), UIntType(UnknownWidth))))
    assert(md5(add) != md5(DoPrim(Add, Seq(b0, b0), Seq(), UnknownType)))
  }

  it should "ignore variable names" in {
    val a =
      """circuit a:
        |  module a:
        |    input x : UInt<1>
        |    output y: UInt<1>
        |    y <= x
        |""".stripMargin

    assert(md5(parse(a)) == md5(parse(a)), "the same circuit should always be equivalent")

    val b =
      """circuit a:
        |  module a:
        |    input abc : UInt<1>
        |    output haha: UInt<1>
        |    haha <= abc
        |""".stripMargin

    assert(md5(parse(a)) == md5(parse(b)), "renaming ports should not affect the hash by default")

    val c =
      """circuit a:
        |  module a:
        |    input x : UInt<1>
        |    output y: UInt<1>
        |    y <= and(x, UInt<1>(0))
        |""".stripMargin

    assert(md5(parse(a)) != md5(parse(c)), "changing an expression should affect the hash")

    val d =
      """circuit c:
        |  module c:
        |    input abc : UInt<1>
        |    output haha: UInt<1>
        |    haha <= abc
        |""".stripMargin

    assert(md5(parse(a)) != md5(parse(d)), "circuits with different names are always different")
    assert(md5(parse(a).modules.head) == md5(parse(d).modules.head),
      "modules with different names can be structurally different")

    // for the Dedup pass we do need a way to take the port names into account
    assert(StructuralHash.md5WithPortNames(parse(a).modules.head) !=
      StructuralHash.md5WithPortNames(parse(b).modules.head),
      "renaming ports does affect the hash if we ask to")
  }


  it should "not ignore port names if asked to" in {
    val e =
      """circuit a:
        |  module a:
        |    input x : UInt<1>
        |    wire y: UInt<1>
        |    y <= x
        |""".stripMargin

    val f =
      """circuit a:
        |  module a:
        |    input z : UInt<1>
        |    wire y: UInt<1>
        |    y <= z
        |""".stripMargin

    val g =
      """circuit a:
        |  module a:
        |    input x : UInt<1>
        |    wire z: UInt<1>
        |    z <= x
        |""".stripMargin

    assert(StructuralHash.md5WithPortNames(parse(e).modules.head) !=
      StructuralHash.md5WithPortNames(parse(f).modules.head),
      "renaming ports does affect the hash if we ask to")
    assert(StructuralHash.md5WithPortNames(parse(e).modules.head) ==
      StructuralHash.md5WithPortNames(parse(g).modules.head),
      "renaming internal wires should never affect the hash")
    assert(md5(parse(e).modules.head) == md5(parse(g).modules.head),
      "renaming internal wires should never affect the hash")
  }

  it should "not ignore port bundle names if asked to" in {
    val e =
      """circuit a:
        |  module a:
        |    input x : {x: UInt<1>}
        |    wire y: {x: UInt<1>}
        |    y.x <= x.x
        |""".stripMargin

    val f =
      """circuit a:
        |  module a:
        |    input x : {z: UInt<1>}
        |    wire y: {x: UInt<1>}
        |    y.x <= x.z
        |""".stripMargin

    val g =
      """circuit a:
        |  module a:
        |    input x : {x: UInt<1>}
        |    wire y: {z: UInt<1>}
        |    y.z <= x.x
        |""".stripMargin

    // TODO: currently this fails because we do not namespace bundle types properly...
    assert(md5(parse(e).modules.head) == md5(parse(f).modules.head),
      "renaming port bundles does normally not affect the hash")
    assert(StructuralHash.md5WithPortNames(parse(e).modules.head) !=
      StructuralHash.md5WithPortNames(parse(f).modules.head),
      "renaming port bundles does affect the hash if we ask to")
    assert(StructuralHash.md5WithPortNames(parse(e).modules.head) ==
      StructuralHash.md5WithPortNames(parse(g).modules.head),
      "renaming internal wire bundles should never affect the hash")
    assert(md5(parse(e).modules.head) == md5(parse(g).modules.head),
      "renaming internal wire bundles should never affect the hash")
  }


  it should "fail on Info" in {
    // it does not make sense to hash Info nodes
    assertThrows[RuntimeException] {
      md5(FileInfo(StringLit("")))
    }
  }

  "Bundles with different field names" should "be structurally equivalent" in {
    def parse(str: String): BundleType = {
      val src =
        s"""circuit c:
          |  module c:
          |    input z: $str
          |""".stripMargin
      val c = firrtl.Parser.parse(src)
      val tpe = c.modules.head.ports.head.tpe
      tpe.asInstanceOf[BundleType]
    }

    val a = "{x: UInt<1>, y: UInt<1>}"
    assert(md5(parse(a)) == md5(parse(a)), "the same bundle should always be equivalent")

    val b = "{z: UInt<1>, y: UInt<1>}"
    assert(md5(parse(a)) == md5(parse(b)), "changing a field name should maintain equivalence")

    val c = "{x: UInt<2>, y: UInt<1>}"
    assert(md5(parse(a)) != md5(parse(c)), "changing a field type should not maintain equivalence")

    val d = "{x: UInt<1>, y: {y: UInt<1>}}"
    assert(md5(parse(a)) != md5(parse(d)), "changing the structure should not maintain equivalence")

    assert(md5(parse("{z: {y: {x: UInt<1>}}, a: UInt<1>}")) == md5(parse("{a: {b: {c: UInt<1>}}, z: UInt<1>}")))
  }


}
