package sorted
import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

/**
    This file contains a decorator for a sorted List[Int], that contains only unique elements (hence, sorted Set)
    It describes a List that is always sorted in *ascending* order
    (i.e. smallest elements first)
*/
sealed abstract class SortedList{
    def size() : BigInt = this match {
        case Nil => 0
        case Cons(x, xs) => 1 + xs.size()
    }

    def isSorted() : Boolean = this match {
        case Nil => true
        case Cons(_,Nil) => true
        case Cons(x1, Cons(x2, xs)) =>
            x1 < x2 && Cons(x2,xs).isSorted()
    }

    def content(): Set[Int] = this match {
        case Nil => Set()
        case Cons(i, t) => Set(i) ++ t.content()
    }

    def contains(e: Int) ={
        // require(size()!=0)
        content().contains(e)
    } 

    def head: Int = { 
        require(this != Nil)
        this match
            case Cons(x, xs) => x
    }
    
    def last: Int = {
        require(this != Nil)
        this match
            case Cons(x, Nil) => x
            case Cons(head, tail) => tail.last
        
    }

    def insert(e : Int) : SortedList = {
        require(isSorted())
        this match {
            case Nil => Cons(e, Nil)
            case Cons(x, xs) if (x == e) => this
            case Cons(x, xs) if (x < e) => Cons(x, xs.insert(e))
            case Cons(x, xs) if (e < x) => Cons(e, Cons(x,xs))
        }
        }.ensuring {(res:SortedList) =>
            res.isSorted() && res.content() == this.content() ++ Set(e)}
    
    def remove(e: Int) : SortedList = {
        require(isSorted())
        // require(size()!=0)
        // require(contains(e))
        this match{
            case Nil => Nil
            case Cons(x, xs) if (x == e) => xs.remove(e)
            case Cons(x, xs) if (x != e)=> Cons(x, xs.remove(e))
        }
    }.ensuring((res:SortedList) =>  res.isSorted() && !res.contains(e))

    def drop(i: Int): SortedList ={
        this match 
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then xs.drop(i-1) else Cons(x, xs)
    }

    def take(i: Int): SortedList = {
        this match
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then Cons(x, xs.take(i-1)) else Nil
    }
}
case object Nil extends SortedList
case class Cons(x: Int, tail: SortedList) extends SortedList


// @ghost
// object ssProperties{
//     import SortedList.*

//     //def insertPreservesUniqueness() = True

// }