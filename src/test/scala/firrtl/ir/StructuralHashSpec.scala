// See LICENSE for license details.

package firrtl.ir

import firrtl.PrimOps._
import org.scalatest._
import firrtl.ir._

class StructuralHashSpec extends FlatSpec {
  private def md5(n: FirrtlNode): HashCode = StructuralHash.md5(n)
  private def parse(circuit: String): Circuit = firrtl.Parser.parse(circuit)

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

  it should "fail on Info" in {
    // it does not make sense to hash Info nodes
    assertThrows[RuntimeException] {
      md5(FileInfo(StringLit("")))
    }
  }


}
