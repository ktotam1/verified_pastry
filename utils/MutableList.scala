package utils
import stainless.annotation.mutable


sealed abstract class MutableList[@mutable T] {
    def :+(e: T): MutableList[T] = {
        MutableCons(e, this)
    }
}

case class MutableCons[@mutable T](head: T, tail: MutableList[T]) extends MutableList[T]
case class MutableNil[@mutable T]() extends MutableList[T]