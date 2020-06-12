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
}
