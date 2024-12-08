package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

/**
    This file contains a decorator for a sorted List[Int], that contains only unique elements (hence, sorted Set)
    It describes a List that is always sorted in *ascending* order
    (i.e. smalles elements first)
*/
sealed abstract class SortedList{
    def size() : Int = this match {
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

    def contains(e: Int) = content().contains(e) 

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
        require(size()!=0)
        require(contains(e))
        this match{
            case Cons(x, xs) if (x == e) => xs
            case Cons(x, xs) if (x != e)=> Cons(x, xs.remove(e))
        }
    }.ensuring((res:SortedList) => res.isSorted() && !res.contains(e))

    def isFirstK(k:Int, e:Int): Boolean = {
        decreases(k)
        if k == 0 then return false

        this match {
            case Nil => false
            case Cons(x,xs) if (x == e) => true
            case Cons(x,xs) if (x < e) => xs.isFirstK(k-1,e)
            case Cons(x,xs) if (e < x) => false
        }
    }

    def isLastK(k:Int,e:Int) : Boolean = {
        /* 
            Since we want to preserve the ordering, we can't simply call `isFirstK` on a reverse-ordered list, since it wouldn't be sorted
            We must therefore be slightly more careful in the implementation
        */
        decreases(this.size())
        if k == 0 then return false
        this match{
            case Nil => false
            case Cons(x,xs) if (x == e) => xs.size() < k
            case Cons(x,xs) if (x < e) => xs.isLastK(k,e) 
            case Cons(x,xs) if (e < x) => false
        }
    }


    def isFirstLastK(k: Int, e: Int): Boolean = {
        /* 
            Return true if element `e` is one amongst the first `k` or last `k` elements of the list
         */
        require(k>=0)
        isFirstK(k,e) || isLastK(k,e)
    }
}
case object Nil extends SortedList
case class Cons(head: Int, tail: SortedList) extends SortedList


@ghost
object ssProperties{

    //def insertPreservesUniqueness() = True

}