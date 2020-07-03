// See LICENSE for license details.

package firrtl.benchmark

import firrtl.analyses.NodeCount
import firrtl.benchmark.util._

object NodeCountBenchmark extends App {
  val inputFile = args(0)
  val input = filenameToCircuit(inputFile)
  print(s"Node count directly after parsing $inputFile: ")
  val count = NodeCount(input).unique
  println(s"$count")
}
