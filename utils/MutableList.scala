package utils
import stainless.annotation.mutable
import stainless.collection.* 
import stainless.lang.*
sealed abstract class MutableList[@mutable T] {
    def :+(e: T): MutableList[T] = {
        MutableCons(e, this)
    }

    def length: Int = {
        //TODO: FIX 
        this match 
            case MutableNil() => 0
            case MutableCons(head, tail) => 1 + tail.length
    }.ensuring(_ >= 0)

    def last(): T = {
        require(this.length > 0)
        decreases(this.length)
        this match 
            case MutableCons(head, MutableNil()) => head
            case MutableCons(head, tail) => tail.last()
    }
    def head: T = {
        require(this.length > 0)
        this match
            case MutableCons(head, tail) => head
        
    }
}

case class MutableCons[@mutable T](x: T, tail: MutableList[T]) extends MutableList[T]
case class MutableNil[@mutable T]() extends MutableList[T]


