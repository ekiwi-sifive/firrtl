// See LICENSE for license details.

package firrtl
package benchmark
package hot

import firrtl.annotations.CircuitTarget
import firrtl.benchmark.util._
import firrtl.transforms.DedupModules

import scala.collection.mutable

object StructuralHashBenchmark extends App {
  val inputFile = args(0)
  val warmup = args(1).toInt
  val runs = args(2).toInt
  val select = args(3)

  val input = filenameToCircuit(inputFile)
  val inputState = CircuitState(input, Seq())

  val preState = new HighFirrtlCompiler().transform(inputState)


  if (select == "old") {
    println("Benchmarking Dedup agnostify and fastSerializedHash followed by String.hashCode.toString")
    hot.util.benchmark(warmup, runs) { oldDedup(preState.circuit) }
  } else if (select == "serializer") {
    println("Benchmarking Dedup agnostify and ir.Serializer.serialize() followed by String.hashCode.toString")
    hot.util.benchmark(warmup, runs) { oldDedupWithNewSerializer(preState.circuit) }
  } else {
    println("Benchmarking new StrucuturalHash")
    hot.util.benchmark(warmup, runs) { structuralHash(preState.circuit) }
  }

  private def structuralHash(c: firrtl.ir.Circuit): Unit = {
    c.modules.foreach { m =>
      val tag = firrtl.ir.StructuralHash.md5WithSignificantPortNames(m)
    }
  }

  private def oldDedup(c: firrtl.ir.Circuit): Unit = {
    val top = CircuitTarget(c.main)
    c.modules.foreach { m =>
      val agnosticRename = RenameMap()
      val agnosticModule = DedupModules.agnostify(top, m, agnosticRename, "thisModule")
      // Build tag
      val builder = new mutable.ArrayBuffer[Any]()

      // It may seem weird to use non-agnostified ports with an agnostified body because
      // technically it would be invalid FIRRTL, but it is logically sound for the purpose of
      // calculating deduplication tags
      val ports = m.ports
      ports.foreach { builder ++= _.serialize }

      agnosticModule match {
        case firrtl.ir.Module(i, n, ps, b) => builder ++= DedupModules.fastSerializedHash(b).toString()
        case firrtl.ir.ExtModule(i, n, ps, dn, p) =>
          builder ++= dn
          p.foreach { builder ++= _.serialize }
      }
      val tag = builder.hashCode().toString
    }
  }

  private def oldDedupWithNewSerializer(c: firrtl.ir.Circuit): Unit = {
    val top = CircuitTarget(c.main)
    c.modules.foreach { m =>
      val agnosticRename = RenameMap()
      val agnosticModule = DedupModules.agnostify(top, m, agnosticRename, "thisModule")
      val tag = firrtl.ir.Serializer.serialize(agnosticModule).hashCode().toString
    }
  }
}