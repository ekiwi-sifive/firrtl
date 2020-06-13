// See LICENSE for license details.

package firrtlTests.ir

import firrtl.ir._
import org.scalatest._

class SerializeSpec extends FlatSpec {
  "FileInfo" should "serialize correctly" in {
    assert(FileInfo(StringLit("test")).serialize == " @[test]")
    assert(FileInfo(StringLit("test.scala:80")).serialize == " @[test.scala:80]")
    assert(FileInfo(StringLit("test.scala:\n80")).serialize == " @[test.scala:\\n80]")
    assert(FileInfo(StringLit("test.scala:]80")).serialize == " @[test.scala:\\]80]")
  }

  "Serializer" should "serialize a module correctly" in {
    val in =
      """circuit m :
        |  module m :
        |    input clk : Clock
        |    input reset : UInt<1>
        |    output x : UInt<1>
        |    clk is invalid
        |    x is invalid
        |""".stripMargin.trim

    val c = firrtl.Parser.parse(in)
    val out = Serializer.serialize(c)
    val outOld = c.serialize
    in.split('\n').zip(out.split('\n')).zip(outOld.split('\n')).zipWithIndex.foreach { case (((il, ol), ool), line) =>
      assert(il == ol, s"failed in line $line")
      assert(ool == ol, s"failed in line $line")
    }
  }
}
