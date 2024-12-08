package sorted
import pastryMath.*
import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

/**
    This file contains a decorator for a sorted List[Int], that contains only unique elements (hence, sorted Set)
    It describes a List that is always sorted in *ascending* order
    (i.e. smallest elements first)
*/
sealed abstract class LeafSet {
    var isLeft: Boolean = true
    var id: Int = 0
    def lt(x:Int,y:Int) = if isLeft then dist(y,id) < dist(x,id) else dist(x,id) < dist(y,id)

    def size() : BigInt = this match {
        case Nil => 0
        case Cons(x, xs) => 1 + xs.size()
    }

    def isSorted() : Boolean = this match {
        case Nil => true
        case Cons(_,Nil) => true
        case Cons(x1, Cons(x2, xs)) =>
            lt(x1,x2) && Cons(x2,xs).isSorted()
    }

    def content(): Set[Int] = this match {
        case Nil => Set()
        case Cons(i, t) => Set(i) ++ t.content()
    }

    def contains(e: Int) = {
        // require(size()!=0)
        content().contains(e)
    } 

    def toList: List[Int] = {
        content().toList
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

    def insert(e : Int) : LeafSet = {
        require(isSorted())
        this match {
            case Nil => Cons(e, Nil)
            case Cons(x, xs) if (x == e) => this
            case Cons(x, xs) if lt(x, e) => Cons(x, xs.insert(e))
            case Cons(x, xs) if lt(e, x) => Cons(e, Cons(x,xs))
        }
        }.ensuring {(res:LeafSet) =>
            res.isSorted() && res.content() == this.content() ++ Set(e)}
    
    def remove(e: Int) : LeafSet = {
        require(isSorted())
        // require(size()!=0)
        // require(contains(e))
        this match{
            case Nil => Nil
            case Cons(x, xs) if (x == e) => xs.remove(e)
            case Cons(x, xs) if (x != e)=> Cons(x, xs.remove(e))
        }
    }.ensuring((res:LeafSet) =>  res.isSorted() && !res.contains(e))

    def drop(i: Int): LeafSet ={
        this match 
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then xs.drop(i-1) else Cons(x, xs)
    }

    def take(i: Int): LeafSet = {
        this match
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then Cons(x, xs.take(i-1)) else Nil
    }
}
case object Nil extends LeafSet
case class Cons(x: Int, tail: LeafSet) extends LeafSet


// @ghost
// object ssProperties{
//     import LeafSet.*

//     //def insertPreservesUniqueness() = True

// }