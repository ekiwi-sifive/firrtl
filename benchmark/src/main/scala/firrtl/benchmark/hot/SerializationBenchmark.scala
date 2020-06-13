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
    println("Benchmarking legacy serialization")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(input.serialize)
  } else if(select == "h") {
    println("Benchmarking md5 hash")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(StructuralHash.md5(input))
  } else if(select == "t") {
    println("Benchmarking md5 hash w/ transitivity")
    firrtl.benchmark.hot.util.benchmark(warmup, runs)(
      StructuralHash.transitiveMd5(input.main, input.modules)
    )
  } else if(select == "test") {
    println("Testing the new serialization against the old one")
    val o = input.serialize.split('\n').filterNot(_.trim.isEmpty)
    val n = Serializer.serialize(input).split('\n').filterNot(_.trim.isEmpty)
    println(input.modules.head.serialize)
    println(input.modules.head.asInstanceOf[firrtl.ir.Module].body)

    println(s"Old lines: ${o.length}")
    println(s"New lines: ${n.length}")
    o.zip(n).zipWithIndex.foreach { case ((ol, nl), ii) =>
      if(ol != nl) {
        println(s"❌@$ii OLD: |$ol|")
        println(s"❌@$ii NEW: |$nl|")
        throw new RuntimeException()
      } else {
        println(s"✅        |$ol")
      }
    }

  }


}
