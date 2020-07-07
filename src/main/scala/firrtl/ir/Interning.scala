// See LICENSE for license details.

package firrtl.ir

/** Helper functions and classes for keeping the number of FirrtlNodes created small.
  *
  * The most important thing to note is: The firrtl compiler does not do **strict** interning,
  * i.e., only because two FirrtlNodes are not `eq`, the could still contain the same data.
  * However, in an effort to reduce the number of object used in the compiler we try to intern
  * often used expressions and types.
  */
object Interning {

}

private[firrtl] class IdSeqKey[T <: AnyRef](val e: Seq[T]) {
  override def equals(obj: Any): Boolean = obj match {
    case other : IdSeqKey[_] => e.zip(other.e).forall{ case (a,b) => a.eq(b) } && e.length == other.e.length
    case _ => false
  }
  override val hashCode: Int = e.map(System.identityHashCode).hashCode()
}
private[firrtl] object IdSeqKey { def apply[T <: AnyRef](e: Seq[T]): IdSeqKey[T] = new IdSeqKey[T](e) }
private[firrtl] class IdAndEqKey[I <: AnyRef, E](val i: I, val e: E) {
  override def equals(obj: Any): Boolean = obj match {
    case other : IdAndEqKey[_, _] => other.i.eq(i) && other.e == e
    case _ => false
  }
  override val hashCode: Int = (System.identityHashCode(i), e).hashCode()
}
private[firrtl] object IdAndEqKey {
  def apply[I <: AnyRef, E](i: I, e: E): IdAndEqKey[I, E] = new IdAndEqKey[I,E](i, e)
}
// TODO: would it make sense to replace Seq[T] with Product[T]?
private[firrtl] class IdSeqAndEqKey[I <: AnyRef, E](val i: Seq[I], val e: E) {
  override def equals(obj: Any): Boolean = obj match {
    case other : IdSeqAndEqKey[_, _] =>
      i.zip(other.i).forall{ case (a,b) => a.eq(b) } && i.length == other.i.length && other.e == e
    case _ => false
  }
  override val hashCode: Int = (i.map(System.identityHashCode).hashCode(), e.hashCode()).hashCode()
}
private[firrtl] object IdSeqAndEqKey {
  def apply[I <: AnyRef, E](i: Seq[I], e: E): IdSeqAndEqKey[I, E] = new IdSeqAndEqKey[I,E](i, e)
}