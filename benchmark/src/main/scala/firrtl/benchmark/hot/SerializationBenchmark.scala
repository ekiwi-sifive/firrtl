// See LICENSE for license details.
package firrtl.benchmark.hot

import firrtl.benchmark.util._
import firrtl.ir.{Serializer, StructuralHash}

object SerializationBenchmark extends App {
  val inputFile = args(0)
  val warmup = args(1).toInt
  val runs = args(2).toInt
  val select = if(args.length > 3) args(3) else "o"

  val input = filenameToCircuit(inputFile)

  if(select == "n") {
    println("Benchmarking new Serializer.serialize")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(Serializer.serialize(input))
  } else if(select == "o") {
    println("Bnechmarking legacy serialization")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(input.serialize)
  } else if(select == "h") {
    println("Bnechmarking md5 hash")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(StructuralHash.md5(input))
  }

}
