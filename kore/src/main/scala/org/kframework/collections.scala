package org.kframework

import collection.JavaConverters._
import java.util.stream.StreamSupport
import scala.collection.mutable.Builder
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.SetBuilder

trait Indexed[I, T] {
  def apply(i: I): T = get(i).get
  def get(i: I): Option[T]
}

trait Collection[T] extends java.lang.Iterable[T] {
  type This <: Collection[T]

  def newBuilder: Builder[T, This]

  def canEqual(that: Any): Boolean

  def foreach(f: T => Unit)

  def mkString(separator: String): String = iterable.mkString(separator)

  def iterable: Iterable[T]

  def iterator = iterable.iterator.asJava
  def list: java.util.List[T] = iterable.toList.asJava
  def stream: java.util.stream.Stream[T] = StreamSupport.stream(iterable.asJava.spliterator(), false)

  def isEmpty: Boolean = size == 0
  def size: Int = { var s = 0; foreach { x => s += 1 }; s }

  def map(f: T => T): This = {
    val builder = newBuilder
    foreach { builder += f(_) }
    builder.result()
  }
  def map[R](f: T => R): scala.List[R] = {
    val builder = ListBuffer[R]()
    foreach { builder += f(_) }
    builder.result()
  }
}


case class ImmutableList[T](l: List[T]) extends Collection[T] with Indexed[Int, T] {
  type This = ImmutableList[T]
  def get(i: Int): Option[T] = l.lift(i)
  override def apply(i: Int): T = l(i)

  def newBuilder: Builder[T, This] = ListBuffer() mapResult { new ImmutableList(_) }

  def foreach(f: T => Unit) = l foreach f

  def iterable: Iterable[T] = l
}

case class ImmutableSet[T](s: collection.Set[T]) extends Collection[T] {
  type This = ImmutableSet[T]

  def newBuilder: Builder[T, This] = new SetBuilder[T, collection.Set[T]](Set[T]()) mapResult { new ImmutableSet(_) }

  def foreach(f: T => Unit) = s foreach f
  def iterable: Iterable[T] = s
}

import org.kframework._
import collection.JavaConverters._
import java.util.stream.StreamSupport

object Collections {
  def immutable[T](s: java.lang.Iterable[T]): Iterable[T] = s.asScala
  def immutable[T](s: java.util.Set[T]): Set[T] = s.asScala.toSet
  def immutable[T](s: java.util.List[T]): Seq[T] = s.asScala
  def immutable[T](s: Array[T]): Seq[T] = s

  def iterable[T](c: Iterable[T]): java.lang.Iterable[T] = c.asJava
  def stream[T](c: Iterable[T]): java.util.stream.Stream[T] = StreamSupport.stream(c.asJava.spliterator(), false);
  def stream[T](c: Collection[T]): java.util.stream.Stream[T] = c.stream
  def iterable[T](c: Collection[T]): java.lang.Iterable[T] = c.iterable.asJava
}
