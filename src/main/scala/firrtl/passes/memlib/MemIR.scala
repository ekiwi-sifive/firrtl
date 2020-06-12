// See LICENSE for license details.

package firrtl.passes
package memlib

import firrtl.ir._

object DefAnnotatedMemory {
  def apply(m: DefMemory): DefAnnotatedMemory = {
    new DefAnnotatedMemory(
      m.info,
      m.name,
      m.dataType,
      m.depth,
      m.writeLatency,
      m.readLatency,
      m.readers,
      m.writers,
      m.readwriters,
      m.readUnderWrite,
      None, // mask granularity annotation
      None  // No reference yet to another memory
    )
  }
}

case class DefAnnotatedMemory(
    info: Info,
    name: String,
    dataType: Type,
    depth: BigInt,
    writeLatency: Int,
    readLatency: Int,
    readers: Seq[String],
    writers: Seq[String],
    readwriters: Seq[String],
    readUnderWrite: ReadUnderWrite.Value,
    maskGran: Option[BigInt],
    memRef: Option[(String, String)] /* (Module, Mem) */
    //pins: Seq[Pin],
    ) extends Statement with IsDeclaration {
  def serialize: String = this.toMem.serialize
  def mapStmt(f: Statement => Statement): Statement = this
  def mapExpr(f: Expression => Expression): Statement = this
  def mapType(f: Type => Type): Statement = this.copy(dataType = f(dataType))
  def mapString(f: String => String): Statement = this.copy(name = f(name))
  def toMem = DefMemory(info, name, dataType, depth,
    writeLatency, readLatency, readers, writers,
    readwriters, readUnderWrite)
  def mapInfo(f: Info => Info): Statement = this.copy(info = f(info))
  def foreachStmt(f: Statement => Unit): Unit = Unit
  def foreachExpr(f: Expression => Unit): Unit = Unit
  def foreachType(f: Type => Unit): Unit = f(dataType)
  def foreachString(f: String => Unit): Unit = f(name)
  def foreachInfo(f: Info => Unit): Unit = f(info)
  override def _hash(h: Hasher): Unit = {
    h.id(-77) ; h(name) ; dataType._hash(h) ; h(depth) ; h(writeLatency) ; h(readLatency)
    h(readers.length) ; readers.foreach(h(_))
    h(writers.length) ; writers.foreach(h(_))
    h(readwriters.length) ; readwriters.foreach(h(_))
    h(readUnderWrite.toString)
    h(maskGran.size) ; maskGran.foreach(h(_))
    h(memRef.size) ; memRef.foreach{ case (a, b) => h(a) ; h(b) }
  }
}
