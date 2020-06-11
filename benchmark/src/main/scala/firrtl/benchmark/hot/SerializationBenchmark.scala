// See LICENSE for license details.
package firrtl.benchmark.hot

import firrtl.benchmark.util._
import firrtl.ir.Serializer

object SerializationBenchmark extends App {
  val inputFile = args(0)
  val warmup = args(1).toInt
  val runs = args(2).toInt
  val useNew = args.length > 3

  val input = filenameToCircuit(inputFile)

  if(useNew) {
    println("Benchmarking new Serializer.serialize")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(Serializer.serialize(input))
  } else {
    println("Bnechmarking legacy serialization")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(input.serialize)
  }

}
