package vp_reform

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import StainlessProperies.*
/**
    This file contains a decorator for a sorted List[Int], that contains only unique elements (hence, sorted Set)
    It describes a List that is always sorted in *ascending* order
    (i.e. smalles elements first)
*/
trait Validator_Ordering[T]:
  def isValid(x:T): Boolean

  def compare(x: T, y: T): Int

  @law def inverse(x: T, y: T): Boolean =
    sign(compare(x, y)) == -sign(compare(y, x))

  @law def transitive(x: T, y: T, z: T): Boolean =
    if (compare(x, y) > 0 && compare(y, z) > 0) then compare(x, z) > 0 else if (compare(x, y) < 0 && compare(y, z) < 0) then compare(x, z) < 0 else true

  @law def consistent(x: T, y: T, z: T): Boolean =
    if compare(x, y) == 0 then sign(compare(x, z)) == sign(compare(y, z)) else true

  @law def equalsMeansEquals(x: T, y: T): Boolean =
    (compare(x, y) == 0) == (x == y)

  final def sign(x: Int): BigInt =
    if x < 0 then -1 else if x > 0 then 1 else 0
end Validator_Ordering

sealed abstract class SortedList[T: Validator_Ordering]{
    extension (t: T) def isValid: Boolean = implicitly[Validator_Ordering[T]].isValid(t)
    extension (t: T) def >(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) > 0
    extension (t: T) def <(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) < 0
    extension (t: T) def >=(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) >= 0
    extension (t: T) def <=(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) <= 0


    final def size() : BigInt = {
        this match {
            case Nil() => BigInt(0)
            case Cons(x, xs) => BigInt(1) + xs.size()
        }
    }.ensuring(r=>(r>=0))

    final def isSorted() : Boolean = this match {
        case Nil() => true
        case Cons(_,Nil()) => true
        case Cons(x1, Cons(x2, xs)) =>
            x1 < x2 && Cons(x2,xs).isSorted()
    }

    final def isSet() : Boolean = this match {
        case Nil() => true
        case Cons(_,Nil()) => true
        case Cons(x1, Cons(x2, xs)) =>
            x1 != x2 && Cons(x2,xs).isSet()
    }

    final def allValid(): Boolean = this match{
        case Nil() => true
        case Cons(x,xs) => x.isValid && xs.allValid()
    }

    final def isValid: Boolean = isSorted() && isSet() && allValid()

    final def content(): Set[T] = this match {
        case Nil() => Set()
        case Cons(i, t) => t.content() + i
    }

    final def contains(e: T): Boolean = {
        this match{
            case Nil() => false
            case Cons(x,xs) => if x == e then true else xs.contains(e)
        }
    }

    final def containsOne(other: SortedList[T]): Boolean = {
        require(isValid)
        require(other.isValid)
        (this, other) match{
            case (Nil(), _) => false
            case (_, Nil()) => false
            case (Cons(x, xs), Cons(y, ys)) => {
                if (x == y) {
                    assert(contains(x) && other.contains(x))
                    true
                } else if (x < y) {
                    xs.containsOne(other)
                } else {
                    this.containsOne(ys)
                }
            }
        }
    }

    final def head: T = { 
        require(this != Nil())
        this match
            case Cons(x, xs) => x
    }

    final def tail: SortedList[T] = {
        require(this != Nil())
        this match {
            case Cons(x, xs) => xs
        }
    }
    
    final def last: T = {
        require(this != Nil())
        this match
            case Cons(x, Nil()) => x
            case Cons(head, tail) => tail.last
        
    }

    final def insert(e : T) : SortedList[T] = {
        require(isValid)
        this match {
            case Nil() => Cons(e, Nil())
            case Cons(x, xs) if (x == e) => this
            case Cons(x, xs) if (x < e) => Cons(x, xs.insert(e))
            case Cons(x, xs) if (e < x) => Cons(e, Cons(x,xs))
        }
    }.ensuring {(res:SortedList[T]) =>
        res.isValid && res.content() == this.content() ++ Set(e) && (size() <= res.size()) && res.size() <= (size() + 1)}
    
    // final def isSubsetOf(other: SortedList[T]): Boolean = {
    //     require(isValid)
    //     require(other.isValid)
    //     forall(k=>other.contains(k))
    // }

    // final def isSubsetOf(other: SortedList[T]): Boolean = {
    //     require(isValid)
    //     require(other.isValid)
    //     this match {
    //         case Nil() => true
    //         case Cons(x, xs) => other.contains(x) && xs.isSubsetOf(other)
    //     }
    // }

    final def isSubsetOf(other: SortedList[T]): Boolean = {
        require(isValid)
        require(other.isValid)
        (this, other) match{
            case (Nil(), _) => true
            case (Cons(x, xs), Nil()) => false
            case (Cons(x, xs), Cons(y, ys)) => {
                if (x == y) {
                    xs.isSubsetOf(ys)
                } else if (x < y) {
                    false
                } else {
                    this.isSubsetOf(ys)
                }
            }
        }
    }

    final def remove(e: T) : SortedList[T] = {
        require(isValid)
        this match{
            case Nil() => Nil()
            case Cons(x, xs) if (x == e) => xs
            case Cons(x, xs) if (x != e) => Cons(x, xs.remove(e))
        }
    }.ensuring((sl:SortedList[T])=> sl.isValid && sl.size() <= this.size())

    final def drop(i: Int): SortedList[T] ={
        require(isValid)
        this match 
            case Nil() => Nil()
            case Cons(x, xs) => if i > 0 then xs.drop(i-1) else Cons(x, xs)
    }.ensuring(_.isValid)

    final def take(i: Int): SortedList[T] = {
        require(isValid)
        this match
            case Nil() => Nil()
            case Cons(x, xs) => if i > 0 then Cons(x, xs.take(i-1)) else Nil()
    }.ensuring(_.isValid)

    final def isFirstK(k:BigInt, e:T): Boolean = {
        require(isValid)
        if k == 0 then return false
        this match {
            case Nil() => false
            case Cons(x,xs) if (x == e) => true
            case Cons(x,xs) if (x < e) => if k>0 then xs.isFirstK(k-1,e) else false
            case Cons(x,xs) if (e < x) => false
        }
    }

    final def isLastK(k:BigInt,e:T) : Boolean = {
        require(isValid)
        /* 
            Since we want to preserve the ordering, we can't simply call `isFirstK` on a reverse-ordered list, since it wouldn't be sorted
            We must therefore be slightly more careful in the implementation
        */
        def inner(lst: SortedList[T]): Boolean = {
            require(lst.isValid)
            //decreases(lst.size())
            if k == 0 then return false
            lst match{
                case Nil() => false
                case Cons(x,xs) if (x == e) => {
                    assert(xs match{
                        case Nil() => true
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

    final def isFirstLastK(k: BigInt, e: T): Boolean = {
        /* 
            Return true if element `e` is one amongst the first `k` or last `k` elements of the list
         */
        require(isValid)
        require(k>=0)
        isFirstK(k,e) || isLastK(k,e)
    }

    final def toStainless() : List[T] = {
        require(isValid)
        def build_recurse(rest: SortedList[T]) : List[T] ={
            require(rest.isValid)
            rest match{
                case vp_reform.Nil() => stainless.collection.Nil()
                case vp_reform.Cons(x, tail) => stainless.collection.Cons(x,build_recurse(tail))
            }
        }.ensuring((ret:List[T]) => isvalidstainless(ret,e=>e))
        build_recurse(this)
    }.ensuring((ret:List[T]) => isvalidstainless(ret,e=>e))

    final def merge(other: SortedList[T]): SortedList[T] ={
        require(isValid)
        require(other.isValid)
        (this,other) match{
            case (Nil(),o) => o
            case (t,Nil()) => t
            case (Cons(x,xs),Cons(y,ys)) =>{
                assert(xs.isValid)
                assert(ys.isValid)
                if x == y then Cons(x,xs.merge(ys))
                else if (x < y) then Cons(x,xs.merge(other))
                else Cons(y,this.merge(ys))  
            }
        }
    }.ensuring((sl:SortedList[T])=> sl.isValid && sl.size() <= (this.size() + other.size()))

    // final def removeAll(from: SortedList[T]): SortedList[T] = {
    //     require(isValid)
    //     require(from.isValid)
    //     from match{
    //         case Nil() => this
    //         case Cons(x,xs) => remove(x).removeAll(xs)
    //     }
    // }.ensuring((sl:SortedList[T])=> sl.isValid)

    final def removeAll(other: SortedList[T]): SortedList[T] = {
        require(isValid)
        require(other.isValid)
        (this,other) match{
            case (Nil(),o) => Nil()
            case (t,Nil()) => t
            case (Cons(x,xs),Cons(y,ys)) =>{
                assert(xs.isValid)
                assert(ys.isValid)
                if x == y then xs.removeAll(ys)
                else if (x < y) then Cons(x,xs.removeAll(other))
                else this.removeAll(ys)
            }
        }
    }.ensuring((sl:SortedList[T])=> sl.isValid && (sl == Nil() || this.head <= sl.head) && sl.size() <= this.size())

    final def forall(p:T=>Boolean): Boolean={
        require(isValid)
        this match{
            case vp_reform.Nil() => true
            case vp_reform.Cons(x, xs) => p(x) && xs.forall(p)
        }
    }

    final def exists(p:T=>Boolean): Boolean={
        require(isValid)
        !forall(!p(_))
    }

    final def set_equals(other: SortedList[T]):Boolean = {
        require(isValid)
        require(other.isValid)
        (this,other) match{
            case (Nil(),Nil()) => true
            case (Cons(x,xs),Cons(y,ys)) => x==y && xs.set_equals(ys)
            case _ => false
        }
    }

    override def equals(other:Any): Boolean = {
        require(isValid)
        other match{
            case sl: SortedList[T] => if sl.isValid then set_equals(sl) else false
            case _ => false
        }
    }

    @library
    final def intersect(other:SortedList[T]): SortedList[T] = {
        require(isValid)
        require(other.isValid)
        decreases(size()+other.size())
        (this,other) match{
            case (Nil(),_) => Nil()
            case (_,Nil()) => Nil()
            case (Cons(x,xs), Cons(y,ys)) =>{
                assert(xs.isValid)
                assert(ys.isValid)
                if x == y then Cons(x,xs.intersect(ys))
                else if x<y then{
                    //x will never be in `other`
                    //therefore x not in interesect
                    xs.intersect(other)
                }
                else{
                    // x>y
                    // y will never be in `this`
                    this.intersect(ys)
                }
            }
        }
    }.ensuring((ret:SortedList[T]) => ret.isValid)

    final def subsetSize(other: SortedList[T]): BigInt = {
        require(isValid)
        require(other.isValid)
        intersect(other).size()
    }
}

case class Nil[T: Validator_Ordering]() extends SortedList[T]
case class Cons[T: Validator_Ordering](x: T, xs: SortedList[T]) extends SortedList[T]

object StainlessProperies{
    extension [T:Validator_Ordering] (t: T) def isValid: Boolean = implicitly[Validator_Ordering[T]].isValid(t)
    extension [T:Validator_Ordering](t: T) def >(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) > 0
    extension [T:Validator_Ordering](t: T) def <(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) < 0
    extension [T:Validator_Ordering](t: T) def >=(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) >= 0
    extension [T:Validator_Ordering](t: T) def <=(other: T): Boolean = implicitly[Validator_Ordering[T]].compare(t, other) <= 0


    def isASet[T: Validator_Ordering](sl:List[T],key:T=>Int): Boolean ={
        sl match{
            case stainless.collection.Cons(x, xs) => {
                xs match
                    case stainless.collection.Cons(xx, xxs) => key(x) != key(xx) && isASet[T](xs,key)  
                    case stainless.collection.Nil() => true
            }
            case stainless.collection.Nil() => true
        }
    }

    def isvalidstainless[K,T: Validator_Ordering](sl:List[K],key:K=>T): Boolean = {
        sl match{
            case stainless.collection.Cons(x, xs) => {
                xs match
                    case stainless.collection.Cons(xx, xxs) => key(x) < key(xx) && isvalidstainless[K,T](xs,key)  
                    case stainless.collection.Nil() => true
            }
            case stainless.collection.Nil() => true
        }
    }

    def fromStainlessSortedList[K,T: Validator_Ordering](s: List[K],key:K=>T): SortedList[T] = {
        require(isvalidstainless[K,T](s,key))
        s match{
            case stainless.collection.Cons(x, xs) => Cons[T](key(x),fromStainlessSortedList(xs,key))
            case stainless.collection.Nil() => Nil[T]()
        }
    }.ensuring((res:SortedList[T]) => res.isValid)

    def isUniqueWRT[K,T: Validator_Ordering](l: List[K],key: K=>SortedList[T]): Boolean = {
        require(l.forall(t=>key(t).isValid))
        def innerIUWRT(acc:SortedList[T], rest: List[K]): Boolean = {
            require(acc.isValid)
            require(rest.forall(t=>key(t).isValid))
            rest match
                case stainless.collection.Nil[T]() => true
                case stainless.collection.Cons(x, xs) => {
                    assert(key(x).isValid)
                    if acc.containsOne(key(x)) then false else innerIUWRT(acc.merge(key(x)),xs)
                } 
        }
        innerIUWRT(vp_reform.Nil(),l)
    }
}
