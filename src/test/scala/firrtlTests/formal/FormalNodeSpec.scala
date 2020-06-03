// See LICENSE for license details.

package firrtlTests.formal

import firrtl._
import firrtl.testutils.FirrtlFlatSpec

class FormalNodeSpec extends FirrtlFlatSpec {
  def compile(in: String): CircuitState = {
    (new VerilogCompiler).compileAndEmit(CircuitState(parse(in), ChirrtlForm, Seq()))
  }

  val wrongWidth =
    """
      |circuit m:
      |  module m:
      |    input in: UInt<2>
      |    assert w = in
      |""".stripMargin

  "assert" should "raise an exception for UInt that is too wide" in {
    println(compile(wrongWidth).getEmittedCircuit.value)
  }

  val wrongSign =
    """
      |circuit m:
      |  module m:
      |    input in: SInt<1>
      |    assert w = in
      |""".stripMargin

  "assert" should "raise an exception for SInt" in {
    println(compile(wrongSign).getEmittedCircuit.value)
  }


  val input =
    """
      |circuit Checking :
      |  module Checking :
      |    input in: UInt<8>
      |    output out: UInt<8>
      |    out <= in
      |    assert areEqual = eq(out, in)
      |
      |""".stripMargin

  "assert node" should "not be removed by deadcode elimination" in {
    val res = (new VerilogCompiler).compileAndEmit(CircuitState(parse(input), ChirrtlForm, Seq()))
    println(res.getEmittedCircuit.value)
  }
}
