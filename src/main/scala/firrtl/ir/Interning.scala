// See LICENSE for license details.

package firrtl.ir

import scala.collection.mutable

/** Helper functions and classes for keeping the number of FirrtlNodes created small.
  *
  * The most important thing to note is: The firrtl compiler does not do **strict** interning,
  * i.e., only because two FirrtlNodes are not `eq`, the could still contain the same data.
  * However, in an effort to reduce the number of object used in the compiler we try to intern
  * often used expressions and types.
  *
  * Our strategy is three fold:
  * 1. We provide interning expression and type factories for use in the protobuf and firrtl parsers.
  * 2. We modify the `mapExpr` and `mapType` methods to only copy of the returned object is not `eq` to the prior value.
  * 3. We provide an object identity based cache so that, e.g., passes that work on expressions can replace
  *    all expression instances 1:1 instead of creating a new node at every place that the expression is used.
  */
object Interning {

}


/** Caches type nodes in order to reduce the number of objects created.
  * @note This class is only useful for parsers, incremental interning is not supported.
  */
class InterningTypeFactory {
  private val intWidths = mutable.HashMap[BigInt, IntWidth]()
  def makeIntWidth(width: BigInt): IntWidth = intWidths.getOrElseUpdate(width, IntWidth(width))

  private val uIntUnknown = UIntType(UnknownWidth)
  def makeUIntWithUnknownWidth: UIntType = uIntUnknown
  private val uInts = mutable.HashMap[BigInt, UIntType]()
  def makeUInt(width: BigInt): UIntType = uInts.getOrElseUpdate(width, UIntType(makeIntWidth(width)))

  private val sIntUnknown = SIntType(UnknownWidth)
  def makeSIntWithUnknownWidth: SIntType = sIntUnknown
  private val sInts = mutable.HashMap[BigInt, SIntType]()
  def makeSInt(width: BigInt): SIntType = sInts.getOrElseUpdate(width, SIntType(makeIntWidth(width)))

  private val analogUnknown = AnalogType(UnknownWidth)
  def makeAnalogWithUnknownWidth: AnalogType = analogUnknown
  private val analogs = mutable.HashMap[BigInt, AnalogType]()
  def makeAnalog(width: BigInt): AnalogType = analogs.getOrElseUpdate(width, AnalogType(makeIntWidth(width)))

  private val fixedUnknown = FixedType(UnknownWidth, UnknownWidth)
  def makeFixedWithUnknownWidthAndPoint: FixedType = fixedUnknown
  private val fixeds = mutable.HashMap[(BigInt, BigInt), FixedType]()
  def makeFixedWithUnknownWidth(point: BigInt): FixedType =
    fixeds.getOrElseUpdate((-1, point), FixedType(UnknownWidth, makeIntWidth(point)))
  def makeFixedWithUnknownPoint(width: BigInt): FixedType =
    fixeds.getOrElseUpdate((width, -1), FixedType(makeIntWidth(width), UnknownWidth))
  def makeFixed(width: BigInt, point: BigInt): FixedType =
    fixeds.getOrElseUpdate((width, point), FixedType(IntWidth(width), makeIntWidth(point)))

  private val fields = mutable.HashMap[IdAndEqKey[Type, (String, Orientation)], Field]()
  def makeField(name: String, flip: Orientation, tpe: Type): Field =
    fields.getOrElseUpdate(IdAndEqKey(tpe, (name, flip)), Field(name, flip, tpe))


  private val bundles = mutable.HashMap[IdSeqKey[Field], BundleType]()
  def makeBundle(fields: Seq[Field]): BundleType = bundles.getOrElseUpdate(IdSeqKey(fields), BundleType(fields))

  // TODO: interval types

  private val vectors = mutable.HashMap[IdAndEqKey[Type, Int], VectorType]()
  def makeVector(tpe: Type, size: Int): VectorType =
    vectors.getOrElseUpdate(IdAndEqKey(tpe, size), VectorType(tpe, size))
}

/** Caches expression nodes in order to reduce the number of objects created.
  * @note This class is only useful for parsers, incremental interning is not supported.
  * @note Since we target parsers, we generate expressions with unknown type.
  */
class InterningExpressionFactory {
  private val references = mutable.HashMap[String, Reference]()
  def makeReference(name: String): Reference = references.getOrElseUpdate(name, Reference(name))

  private val subFields = mutable.HashMap[String, SubField]()
  private val oldSubFields = mutable.HashMap[String, List[SubField]]()
  def makeSubField(expr: Expression, name: String): SubField = {
    val key = expr.serialize + "." + name
    val newHit = subFields.contains(key)
    val r = subFields.getOrElseUpdate(key, SubField(expr, name))

    // DEBUG: also do old insertion method
    val candidates = oldSubFields.getOrElse(name, List())
    var oldHit = true
    candidates.find(_.expr.eq(expr)).getOrElse {
      oldHit = false
      oldSubFields(name) = candidates :+ r
    }
    if(newHit != oldHit) {
      println(candidates)
    }

    r
  }

  def printStatistics(): Unit = {
    val newCount = subFields.size
    val oldCount = oldSubFields.map(_._2.length).sum
    println(s"Count: $newCount vs $oldCount")

    val newNames = subFields.map(_._2.name).toSet
    println(s"SubField Names: ${newNames.size} vs ${oldSubFields.size}")

    val oldValid = oldSubFields("valid")
    val uniqueSerializeOldValid = oldValid.map(_.expr.serialize).toSet
    println(s"OldValid: ${oldValid.size} vs OldValid with unique serialization ${uniqueSerializeOldValid.size}")

    val nameToObjects = oldValid.groupBy(_.expr.serialize)
    val moreThan10 = nameToObjects.filter(_._2.length > 10)
    moreThan10.take(10).foreach{ case (k,v) => println(s"$k: ${v.mkString(", ")}") }


//    val sorted = subFields.toSeq.sortBy(_._2.length)
//    sorted.foreach { case (name, fields) =>
//      println(s"SubField $name: ${fields.length}")
//    }
  }

//  private val subFields = mutable.HashMap[IdAndEqKey[Expression, String], SubField]()
//  def makeSubField(expr: Expression, name: String): SubField = {
//    val key = IdAndEqKey(expr, name)
//    subFields.getOrElseUpdate(key, SubField(expr, name, UnknownType))
//  }

  private val idSubIndices = mutable.HashMap[IdAndEqKey[Expression, Int], SubIndex]()
  private val subIndices = mutable.HashMap[String, SubIndex]()
  def makeSubIndex(expr: Expression, value: Int): SubIndex = {
    val key = expr.serialize + "[" + value + "]"
    val newHit = subIndices.contains(key)
    val oldKey = IdAndEqKey(expr, value)
    val oldHit = idSubIndices.contains(oldKey)
    idSubIndices.getOrElseUpdate(oldKey, SubIndex(expr, value, UnknownType))

    if(newHit != oldHit) {
      println(key)
    }

    subIndices.getOrElseUpdate(key, SubIndex(expr, value, UnknownType))
  }

  private val subAccesses = mutable.HashMap[IdSeqKey[Expression], SubAccess]()
  def makeSubAccess(expr: Expression, index: Expression): SubAccess =
    subAccesses.getOrElseUpdate(IdSeqKey(List(expr, index)), SubAccess(expr, index, UnknownType))

  private val muxes = mutable.HashMap[IdSeqKey[Expression], Mux]()
  def makeMux(cond: Expression, tval: Expression, fval: Expression): Mux =
    muxes.getOrElseUpdate(IdSeqKey(List(cond, tval, fval)), Mux(cond, tval, fval, UnknownType))

  private val doPrims = mutable.HashMap[IdSeqAndEqKey[Expression, (PrimOp, Seq[BigInt])], DoPrim]()
  def makeDoPrim(op: PrimOp, args: Seq[Expression], consts: Seq[BigInt]): DoPrim =
    doPrims.getOrElseUpdate(IdSeqAndEqKey(args, (op, consts)), DoPrim(op, args, consts, UnknownType))

  private val validIfs = mutable.HashMap[IdSeqKey[Expression], ValidIf]()
  def makeValifId(cond: Expression, value: Expression): ValidIf =
    validIfs.getOrElseUpdate(IdSeqKey(Seq(cond, value)), ValidIf(cond, value, UnknownType))

  private val uIntUnknown = mutable.HashMap[BigInt, UIntLiteral]()
  def makeUIntWithUnknownWidth(value: BigInt): UIntLiteral =
    uIntUnknown.getOrElseUpdate(value, UIntLiteral(value, UnknownWidth))

  private val uIntLits = mutable.HashMap[String, UIntLiteral]()
  def makeUInt(value: BigInt, width: IntWidth): UIntLiteral =
    uIntLits.getOrElseUpdate(value + "." + width.width, UIntLiteral(value, width))

  private val sIntLits = mutable.HashMap[IdAndEqKey[Width, BigInt], SIntLiteral]()
  def makeSInt(value: BigInt, width: Width = UnknownWidth): SIntLiteral =
    sIntLits.getOrElseUpdate(IdAndEqKey(width, value), SIntLiteral(value, width))

  private val fixedLits = mutable.HashMap[IdSeqAndEqKey[Width, BigInt], FixedLiteral]()
  def makeFixedLiteral(value: BigInt, width: Width, point: Width): FixedLiteral =
    fixedLits.getOrElseUpdate(IdSeqAndEqKey(Seq(width, point), value), FixedLiteral(value, width, point))
}



private class IdSeqKey[T <: AnyRef](val e: Seq[T]) {
  override def equals(obj: Any): Boolean = obj match {
    // todo: what if e and i are of different lengths?
    case i : IdSeqKey[_] => e.zip(i.e).forall{ case (a,b) => a.eq(b) } && e.length == i.e.length
    case _ => false
  }
  override val hashCode: Int = e.map(System.identityHashCode).hashCode()
}
private object IdSeqKey { def apply[T <: AnyRef](e: Seq[T]): IdSeqKey[T] = new IdSeqKey[T](e) }
private class IdKey[T <: AnyRef](val k: T) {
  override def equals(obj: Any): Boolean = obj match {
    case i : IdKey[_] => i.eq(k)
    case _ => false
  }
  override val hashCode: Int = System.identityHashCode(k)
}
private object IdKey { def apply[T <: AnyRef](e: T): IdKey[T] = new IdKey[T](e) }
private class IdAndEqKey[I <: AnyRef, E](val i: I, val e: E) {
  override def equals(obj: Any): Boolean = obj match {
    case i : IdAndEqKey[_, _] =>
      def sameId = i.i.eq(this.i)
      def sameData = i.e == this.e
      sameId && sameData
    case _ => false
  }
  override val hashCode: Int = (System.identityHashCode(i), e).hashCode()
}
private object IdAndEqKey {
  def apply[I <: AnyRef, E](i: I, e: E): IdAndEqKey[I, E] = new IdAndEqKey[I,E](i, e)
}
private class IdSeqAndEqKey[I <: AnyRef, E](val i: Seq[I], val e: E) {
  override def equals(obj: Any): Boolean = obj match {
    case o : IdSeqAndEqKey[_, _] =>
      i.zip(o.i).forall{ case (a,b) => a.eq(b) } && i.length == o.i.length && o.e == e
    case _ => false
  }
  override val hashCode: Int = (i.map(System.identityHashCode).hashCode(), e.hashCode()).hashCode()
}
private object IdSeqAndEqKey {
  def apply[I <: AnyRef, E](i: Seq[I], e: E): IdSeqAndEqKey[I, E] = new IdSeqAndEqKey[I,E](i, e)
}