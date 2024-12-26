package utils
import stainless.annotation.mutable


sealed abstract class MutableList[@mutable T] {
    def :+(e: T): MutableList[T] = {
        MutableCons(e, this)
    }

    def length: Int = {
        this match 
            case MutableNil() => 0
            case MutableCons(head, tail) => 1 + tail.length
    }

    def last(): T = {
        require(this.length > 0)
        this match 
            case MutableCons(head, MutableNil()) => head
            case MutableCons(head, tail) => tail.last()
    }
}

case class MutableCons[@mutable T](head: T, tail: MutableList[T]) extends MutableList[T]
case class MutableNil[@mutable T]() extends MutableList[T]