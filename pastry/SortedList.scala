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
    final def size() : BigInt = {
        this match {
            case Nil => BigInt(0)
            case Cons(x, xs) => BigInt(1) + xs.size()
        }
    }.ensuring(r=>(r>=0))

    final def isSorted() : Boolean = this match {
        case Nil => true
        case Cons(_,Nil) => true
        case Cons(x1, Cons(x2, xs)) =>
            x1 < x2 && Cons(x2,xs).isSorted()
    }

    final def isSet() : Boolean = this match {
        case Nil => true
        case Cons(_,Nil) => true
        case Cons(x1, Cons(x2, xs)) =>
            x1 != x2 && Cons(x2,xs).isSet()
    }

    final def isValid: Boolean = isSorted() && isSet()

    final def content(): Set[Int] = this match {
        case Nil => Set()
        case Cons(i, t) => Set(i) ++ t.content()
    }

    final def contains(e: Int): Boolean = {
        this match{
            case Nil => false
            case Cons(x,xs) => if x == e then true else xs.contains(e)
        }
    } 

    final def head: Int = { 
        require(this != Nil)
        this match
            case Cons(x, xs) => x
    }
    
    final def last: Int = {
        require(this != Nil)
        this match
            case Cons(x, Nil) => x
            case Cons(head, tail) => tail.last
        
    }

    final def insert(e : Int) : SortedList = {
        require(isValid)
        this match {
            case Nil => Cons(e, Nil)
            case Cons(x, xs) if (x == e) => this
            case Cons(x, xs) if (x < e) => Cons(x, xs.insert(e))
            case Cons(x, xs) if (e < x) => Cons(e, Cons(x,xs))
        }
    }.ensuring {(res:SortedList) =>
        res.isValid && res.content() == this.content() ++ Set(e) && (size() <= res.size()) && res.size() <= (size() + 1)}
    
    final def remove(e: Int) : SortedList = {
        require(isValid)
        this match{
            case Nil => Nil
            case Cons(x, xs) if (x == e) => xs
            case Cons(x, xs) if (x != e)=> Cons(x, xs.remove(e))
        }
    }.ensuring((res:SortedList) =>  res.isValid)

    final def drop(i: Int): SortedList ={
        require(isValid)
        this match 
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then xs.drop(i-1) else Cons(x, xs)
    }.ensuring((res:SortedList) => res.isSorted())

    final def take(i: Int): SortedList = {
        require(isValid)
        this match
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then Cons(x, xs.take(i-1)) else Nil
    }.ensuring((res:SortedList) => res.isSorted())

    final def isFirstK(k:BigInt, e:Int): Boolean = {
        require(isValid)
        if k == 0 then return false
        this match {
            case Nil => false
            case Cons(x,xs) if (x == e) => true
            case Cons(x,xs) if (x < e) => if k>0 then xs.isFirstK(k-1,e) else false
            case Cons(x,xs) if (e < x) => false
        }
    }

    final def isLastK(k:BigInt,e:Int) : Boolean = {
        require(isValid)
        /* 
            Since we want to preserve the ordering, we can't simply call `isFirstK` on a reverse-ordered list, since it wouldn't be sorted
            We must therefore be slightly more careful in the implementation
        */
        def inner(lst: SortedList): Boolean = {
            require(lst.isValid)
            //decreases(lst.size())
            if k == 0 then return false
            lst match{
                case Nil => false
                case Cons(x,xs) if (x == e) => {
                    assert(xs match{
                        case Nil => true
                        case _ => xs.head != e
                    })
                    return xs.size() < k 
                }
                case Cons(x,xs) if (x < e) => {
                    assert(xs.size() < lst.size())
                    inner(xs)
                } 
                case Cons(x,xs) if (e < x) => false
            }
        }
        inner(this)
    }

    final def isFirstLastK(k: BigInt, e: Int): Boolean = {
        /* 
            Return true if element `e` is one amongst the first `k` or last `k` elements of the list
         */
        require(isValid)
        require(k>=0)
        isFirstK(k,e) || isLastK(k,e)
    }

    final def toStainless() : List[Int] = {
        require(isValid)
        def build_recurse(rest: SortedList) : List[Int] ={
            require(rest.isValid)
            rest match{
                case vp.Nil => stainless.collection.Nil()
                case vp.Cons(x, tail) => stainless.collection.Cons(x,build_recurse(tail))
            }
        }.ensuring((ret:List[Int]) => isvalidstainless(ret,e=>e))
        build_recurse(this)
    }.ensuring((ret:List[Int]) => isvalidstainless(ret,e=>e))

    final def merge(other: SortedList): SortedList ={
        require(isValid)
        require(other.isValid)
        (this,other) match{
            case (Nil,o) => o
            case (t,Nil) => t
            case (Cons(x,xs),Cons(y,ys)) =>{
                assert(xs.isValid)
                assert(ys.isValid)
                if x == y then Cons(x,xs.merge(ys))
                else if (x < y) then Cons(x,xs.merge(other))
                else Cons(y,this.merge(ys))  
            }
        }
    }.ensuring((sl:SortedList)=> sl.isValid)

    final def forall(p:Int=>Boolean): Boolean={
        require(isValid)
        this match{
            case vp.Nil => true
            case vp.Cons(x, xs) => p(x) && xs.forall(p)
        }
    }

    final def exists(p:Int=>Boolean): Boolean={
        require(isValid)
        this match{
            case vp.Nil => true
            case vp.Cons(x, xs) => p(x) || xs.exists(p)
        }
    }

    //def findClosest(e:Int): Boolean
}
case object Nil extends SortedList
case class Cons(x: Int, tail: SortedList) extends SortedList

def isvalidstainless[T](sl:List[T],key:T=>Int): Boolean = {
    sl match{
        case stainless.collection.Cons(x, xs) => {
            xs match
                case stainless.collection.Cons(xx, xxs) => key(x) < key(xx) && isvalidstainless[T](xs,key)  
                case stainless.collection.Nil() => true
        }
        case stainless.collection.Nil() => true
    }
}

def fromStainlessSortedList[T](s: List[T],key:T=>Int): SortedList = {
    require(isvalidstainless[T](s,key))
    s match{
        case stainless.collection.Cons(x, xs) => Cons(key(x),fromStainlessSortedList(xs,key))
        case stainless.collection.Nil() => Nil
    }
}.ensuring((res:SortedList) => res.isValid)

@ghost
object slProperties{

    def isFirstOneEqualIsHead(sl: SortedList,e:Int):Unit = {
        require(sl.isValid)
        require(sl.size() > 0)
    }.ensuring((sl.head == e) == sl.isFirstK(1,e) )

    def nnHasPosSize(sl:SortedList): Unit = {
        require(sl!=Nil)
    }.ensuring(sl.size()>0)

    def isFirstImpliesContains(sl:SortedList,e:Int, k: BigInt): Unit = {
        require(sl.isValid)
        require(sl.size() > 0)
        require(k>=0)
        require(sl.isFirstK(k,e))
        sl match {
            case Nil => assert(false)
            case Cons(x,Nil) if (x!=e) => assert(false) 
            case Cons(x,xs) if x==e =>{
                assert(sl.contains(e))
            } 
            case Cons(x,xs) => {
                assert(xs.size() > 0)
                isFirstImpliesContains(xs,e,k-1)
            }
        }
    }.ensuring(sl.contains(e))

    def isLastImpliesContains(sl:SortedList,e:Int, k: BigInt): Unit = {
        require(sl.isValid)
        require(sl.size() > 0)
        require(k>=0)
        require(sl.isLastK(k,e))
        sl match {
            case Nil => assert(false)
            case Cons(x,Nil) if (x!=e) => assert(false) 
            case Cons(x,xs) if x==e =>{
                assert(sl.contains(e))
            } 
            case Cons(x,xs) => {
                assert(xs.size() > 0)
                isLastImpliesContains(xs,e,k)
            }
        }
    }.ensuring(sl.contains(e))
    
    // def isLastOneEqualIsLast(sl: SortedList,e:Int):Unit = {
    //     require(sl.isValid)
    //     require(sl.size() > 0)
    // }.ensuring((sl.last == e) == sl.isLastK(1,e) )
    def isFirstLastImpliesContains(sl:SortedList,e:Int, k: BigInt): Unit = {
        require(sl.isValid)
        require(sl.size() > 0)
        require(k>=0)
        require(sl.isFirstLastK(k,e))
        assert(sl.isFirstK(k,e) || sl.isLastK(k,e))
        if sl.isFirstK(k,e) then isFirstImpliesContains(sl,e,k) else isLastImpliesContains(sl,e,k)
    }.ensuring(sl.contains(e))

    def removeElementYouContainDecreasesSize(sl: SortedList,e:Int,l:BigInt): Unit = {
        require(sl.contains(e))
        require(sl.isValid)
        require(sl.size() == l)
        decreases(l)
        sl match{
            case Nil =>
            case Cons(x,xs) => {
                if x!=e then removeElementYouContainDecreasesSize(xs,e,l-1)
            }
        }
    }.ensuring(sl.remove(e).size() == l-1)

    def insertNewElementIncreasesSize(sl: SortedList,e:Int,l:BigInt): Unit = {
        require(!sl.contains(e))
        require(sl.isValid)
        require(sl.size() == l)
        sl match{
            case vp.Nil => 
            case vp.Cons(x, tail) => if x<e then insertNewElementIncreasesSize(tail,e,l-1) 
        }
    }.ensuring(sl.insert(e).size() == l+1)

    def removedImpliesDoesNotContain(sl: SortedList,e:Int): Unit = {
        require(sl.isValid)
        sl match {
            case Nil =>
            case Cons(x,Nil) =>
            case Cons(x,Cons(xx,xs)) => {
                if x != e then {
                    removedImpliesDoesNotContain(Cons(xx,xs),e)
                }
                else{
                    validListTailDoesNotContainSmallerElement(Cons(x,Cons(xx,xs)),e)
                }
            }
        }
    }.ensuring(!sl.remove(e).contains(e))

    def validListTailDoesNotContainSmallerElement(sl_cons:Cons,e:Int): Unit = {
        require((sl_cons:SortedList).isValid)
        require(sl_cons.contains(e))
        require(sl_cons.head == e)
        sl_cons match{
            case vp.Cons(x, tail) => {
                assert(x == e)
                assert(tail.isValid)
                vsosaImplNotContain(tail,e)
            }
        }
    }.ensuring(!sl_cons.tail.contains(e))

    def vsosaImplNotContain(sl:SortedList,e:Int): Unit ={
        require(sl.isValid)
        require(sl == Nil || e<sl.head)
        validSmallerOneSmallerAll(sl,e)
        sl match{
            case vp.Nil =>
            case vp.Cons(x, tail) => {
                assert(e!=x)
                vsosaImplNotContain(tail,e)
            }
        }
    }.ensuring(!sl.contains(e))

    def validSmallerOneSmallerAll(sl:SortedList,e:Int): Unit={
        require(sl.isValid)
        require(sl == Nil || e<sl.head)
        
        sl match{
            case vp.Nil =>
            case vp.Cons(x,Nil) =>
            case vp.Cons(x,xs)=>{
                validSmallerOneSmallerAll(xs,e)
            }
        }
    }.ensuring(sl.forall(elem=>e<elem))

    def zncImplremoveNc(sl: SortedList, e:Int, k:Int): Unit = {
        require(sl.isValid)
        require(!sl.contains(e))
        require(k!=e)
        sl match{
            case vp.Nil => 
            case vp.Cons(x, xs) => zncImplremoveNc(xs,e,k)
        }
    }.ensuring(!sl.remove(k).contains(e))
}