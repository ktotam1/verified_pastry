package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import StainlessProperies.*
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
        case Cons(i, t) => t.content() + i
    }

    final def contains(e: Int): Boolean = {
        this match{
            case Nil => false
            case Cons(x,xs) => if x == e then true else xs.contains(e)
        }
    }

    final def containsOne(other: SortedList): Boolean = {
        other match{
            case vp.Nil => false
            case vp.Cons(x, xs) => contains(x) || containsOne(xs) 
        }
    }

    final def head: Int = { 
        require(this != Nil)
        this match
            case Cons(x, xs) => x
    }

    final def tail: SortedList = {
        require(this != Nil)
        this match {
            case Cons(x, xs) => xs
        }
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
    
    // final def isSubsetOf(other: SortedList): Boolean = {
    //     require(isValid)
    //     require(other.isValid)
    //     forall(k=>other.contains(k))
    // }

    // final def isSubsetOf(other: SortedList): Boolean = {
    //     require(isValid)
    //     require(other.isValid)
    //     this match {
    //         case Nil => true
    //         case Cons(x, xs) => other.contains(x) && xs.isSubsetOf(other)
    //     }
    // }

    final def isSubsetOf(other: SortedList): Boolean = {
        require(isValid)
        require(other.isValid)
        (this, other) match{
            case (Nil, _) => true
            case (Cons(x, xs), Nil) => false
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

    final def remove(e: Int) : SortedList = {
        require(isValid)
        this match{
            case Nil => Nil
            case Cons(x, xs) if (x == e) => xs
            case Cons(x, xs) if (x != e) => Cons(x, xs.remove(e))
        }
    }.ensuring(_.isValid)

    final def drop(i: Int): SortedList ={
        require(isValid)
        this match 
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then xs.drop(i-1) else Cons(x, xs)
    }.ensuring(_.isValid)

    final def take(i: Int): SortedList = {
        require(isValid)
        this match
            case Nil => Nil
            case Cons(x, xs) => if i > 0 then Cons(x, xs.take(i-1)) else Nil
    }.ensuring(_.isValid)

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

    final def removeAll(from: SortedList): SortedList = {
        require(isValid)
        require(from.isValid)
        from match{
            case Nil => this
            case Cons(x,xs) => remove(x).removeAll(xs)
        }
    }.ensuring(ret => ret.isValid)

    final def forall(p:Int=>Boolean): Boolean={
        require(isValid)
        this match{
            case vp.Nil => true
            case vp.Cons(x, xs) => p(x) && xs.forall(p)
        }
    }

    final def exists(p:Int=>Boolean): Boolean={
        require(isValid)
        !forall(!p(_))
    }

    final def set_equals(other: SortedList):Boolean = {
        require(isValid)
        require(other.isValid)
        (this,other) match{
            case (Nil,Nil) => true
            case (Cons(x,xs),Cons(y,ys)) => x==y && xs.set_equals(ys)
            case _ => false
        }
    }

    override def equals(other:Any): Boolean = {
        require(isValid)
        other match{
            case sl: SortedList => if sl.isValid then set_equals(sl) else false
            case _ => false
        }
    }

    @library
    final def intersect(other:SortedList): SortedList = {
        require(isValid)
        require(other.isValid)
        decreases(size()+other.size())
        (this,other) match{
            case (Nil,_) => Nil
            case (_,Nil) => Nil
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
    }.ensuring((ret:SortedList) => ret.isValid)

    final def subsetSize(other: SortedList): BigInt = {
        require(isValid)
        require(other.isValid)
        intersect(other).size()
    }
}
case object Nil extends SortedList
case class Cons(x: Int, xs: SortedList) extends SortedList


object StainlessProperies{
    def isASet[T](sl:List[T],key:T=>Int): Boolean ={
        sl match{
            case stainless.collection.Cons(x, xs) => {
                xs match
                    case stainless.collection.Cons(xx, xxs) => key(x) != key(xx) && isASet[T](xs,key)  
                    case stainless.collection.Nil() => true
            }
            case stainless.collection.Nil() => true
        }
    }

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

    def isUniqueWRT[T](l: List[T],key: T=>SortedList): Boolean = {
        require(l.forall(t=>key(t).isValid))
        def innerIUWRT(acc:SortedList, rest: List[T]): Boolean = {
            require(acc.isValid)
            require(rest.forall(t=>key(t).isValid))
            rest match
                case stainless.collection.Nil[T]() => true
                case stainless.collection.Cons(x, xs) => {
                    assert(key(x).isValid)
                    if acc.containsOne(key(x)) then false else innerIUWRT(acc.merge(key(x)),xs)
                } 
        }
        innerIUWRT(vp.Nil,l)
    }
}

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

    def ncImplremoveNc(sl: SortedList, e:Int, k:Int): Unit = {
        require(sl.isValid)
        require(!sl.contains(e))
        sl match{
            case vp.Nil => 
            case vp.Cons(x, xs) => ncImplremoveNc(xs,e,k)
        }
    }.ensuring(!sl.remove(k).contains(e))

    def keySmallerImpliesNEQ[T](key:T=>Int, e1:T,e2:T): Unit={
        require(key(e1)<key(e2))
    }.ensuring(key(e1)!=key(e2))

    def validSLImpliesSet[T](sl:List[T],key:T=>Int):Unit={
        require(isvalidstainless(sl,key))
        sl match {
            case stainless.collection.Nil[T]() => 
            case stainless.collection.Cons[T](x, xs) => {
                xs match{
                    case stainless.collection.Nil() => 
                    case stainless.collection.Cons(xx, xxs) => {
                        assert(key(x)<key(xx))
                        keySmallerImpliesNEQ(key,x,xx)
                        validSLImpliesSet(xs,key)
                    } 
                }
            } 
        }
    }.ensuring(isASet(sl,key))

    def subsetReflexivity(l:SortedList): Unit = {
        require(l.isValid)
        l match {
            case Nil => ()
            case Cons(x, xs) => {
                assert(l.contains(x))
                subsetReflexivity(xs)
            }
        }        
    }.ensuring(l.isSubsetOf(l))

    def strongTailsSubset(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.isSubsetOf(l2))
        require(l1 != Nil)
        require(l2 != Nil)
        if (l1.isSubsetOf(l2.tail)) leftTailSubset(l1, l2.tail)
    }.ensuring(l1.tail.isSubsetOf(l2.tail))


    def appendLeftStillContains(l: SortedList, newhead: Int, e: Int): Unit = {
        require(l.isValid)
        require(l.contains(e))
        require(Cons(newhead, l).isValid)
    }.ensuring(Cons(newhead, l).contains(e))

    def appendLeftContainsNewHead(l: SortedList, newhead: Int): Unit = {
        require(l.isValid)
        require(Cons(newhead, l).isValid)
    }.ensuring(Cons(newhead, l).contains(newhead))

    def forallLeftAppendStillContains(l1: SortedList, l2: SortedList, newhead: Int): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(Cons(newhead, l2).isValid)
        require(l1.forall(k => l2.contains(k)))
        l1 match {
            case Nil => ()
            case Cons(x, xs) => {
                forallLeftAppendStillContains(xs, l2, newhead)
            }
        }
    }.ensuring(l1.forall(k => Cons(newhead, l2).contains(k)))

    def subsetContainAll(l1: SortedList, l2: SortedList) : Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.isSubsetOf(l2))
        decreases(l2.size())
        (l1, l2) match {
            case (Nil, _) => ()
            case (Cons(x, xs), Cons(y, ys)) => {
                if (x == y) {
                    assert(l2.contains(x))
                    strongTailsSubset(l1, l2)
                    subsetContainAll(xs, ys)
                    assert(xs.forall(k => ys.contains(k)))
                    forallLeftAppendStillContains(xs, ys, y)
                    assert(xs.forall(k => Cons(y, ys).contains(k)))
                    assert(Cons(x, xs).forall(k => Cons(y, ys).contains(k)))
                } else {
                    subsetContainAll(l1, ys)
                    forallLeftAppendStillContains(l1, ys, y)
                }
            }
        }
    }.ensuring(l1.forall(k => l2.contains(k)))

    def leftTailForallHolds(l1: SortedList, p: Int=>Boolean): Unit = {
        require(l1.isValid)
        require(l1 != Nil)
        require(l1.forall(p))
    }.ensuring(l1.tail.forall(p))

    def leftTailForallContains(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1 != Nil)
        require(l1.forall(k=>l2.contains(k)))
        leftTailForallHolds(l1, k=>l2.contains(k))
    }.ensuring(l1.tail.forall(k => l2.contains(k)))

    def headGreaterImplNotContains(l: SortedList, e: Int): Unit = {
        // Is equivalent to vsosa

        require(l.isValid)
        require(l != Nil)
        require(l.head > e)
        l match {
            case Cons(x, Nil) => ()
            case Cons(x, xs) => {
                assert(x > e)
                headGreaterImplNotContains(xs, e)
            }
        }
    }.ensuring(!l.contains(e))

    def containsImplHeadLessEql(l: SortedList, e: Int): Unit = {
        require(l.isValid)
        require(l.contains(e))
        if (l.head > e) {
            headGreaterImplNotContains(l, e)
        }
    }.ensuring(e >= l.head)

    def forallContainsImplHeadGreaterEql(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.forall(k=>l2.contains(k)))
        require(l1 != Nil)

        assert(l2.contains(l1.head))
        containsImplHeadLessEql(l2, l1.head)
    }.ensuring(l1.head >= l2.head)

    def containsAndHeadNotEqlImplTailContains(l: SortedList, e: Int): Unit = {
        require(l.isValid)
        require(l.contains(e))
        require(l.head != e)
    }.ensuring(l.tail.contains(e))

    def forallContainsAndHeadNotEqlImplRightTailsForallContains(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1 != Nil)
        require(l1.forall(k=>l2.contains(k)))
        require(l1.head != l2.head)
        l1 match {
            case Cons(x, Nil) => {
                assert(l2.contains(x))
                containsAndHeadNotEqlImplTailContains(l2, x)
            }
            case Cons(x, xs) => {
                leftTailForallContains(l1, l2)
                containsImplHeadLessEql(l2, x)
                assert(l2.head <= x)
                assert(x < xs.head) 
                assert(xs.head > l2.head)
                forallContainsAndHeadNotEqlImplRightTailsForallContains(xs, l2)
            }
        }
    }.ensuring(l1.forall(k=>l2.tail.contains(k)))

    def tailsForallContains(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1 != Nil)
        require(l2 != Nil)
        require(l1.forall(k=>l2.contains(k)))
        decreases(l1.size())

        (l1, l2) match {
            case (Cons(x, Nil), Cons(y, _)) => ()
            case (Cons(x, xs), Cons(y, ys)) => {
                assert(xs != Nil)
                assert(ys != Nil)
                leftTailForallContains(l1, l2)
                assert(xs.forall(k => l2.contains(k)))
                forallContainsImplHeadGreaterEql(l1, l2)
                assert(x >= l2.head)
                assert(xs.head > x)
                assert(xs.head != l2.head)
                forallContainsAndHeadNotEqlImplRightTailsForallContains(xs, l2)
                assert(xs.forall(k => ys.contains(k)))
                tailsForallContains(xs, ys)
            }
        }

    }.ensuring(l1.tail.forall(k=>l2.tail.contains(k)))

    def forallContainsSubset(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.forall(k => l2.contains(k)))
        decreases(l2.size())
        (l1, l2) match{
            case (Nil, _) => ()
            case (Cons(x, xs), Cons(y, ys)) => {
                if (x == y) {
                    tailsForallContains(l1, l2)
                    forallContainsSubset(xs, ys)
                } else {
                    forallContainsAndHeadNotEqlImplRightTailsForallContains(l1, l2)
                    forallContainsSubset(l1, ys)
                }
            }
        }
    }.ensuring(l1.isSubsetOf(l2))

    def mergeSubsetPreservation(a:SortedList, b:SortedList, c:SortedList): Unit = {
        require(a.isValid)
        require(b.isValid)
        require(c.isValid)
        require(a.isSubsetOf(c))
        require(b.isSubsetOf(c))
        decreases(a.merge(b).size())

        (a, b) match {
            case (Nil, _) => {
                assert(a.merge(b) == b)
                assert(b.isSubsetOf(c))
                assert(a.merge(b).isSubsetOf(c))
            }
            case (_, Nil) => {
                assert(a.merge(b) == a)
                assert(a.isSubsetOf(c))
                assert(a.merge(b).isSubsetOf(c))
            }
            case (Cons(ah, at), Cons(bh, bt)) => {
                assert(at.isValid)
                assert(bt.isValid)
                subsetContainAll(a, c)
                subsetContainAll(b, c)
                val ret = a.merge(b)
                if (ah == bh) {
                    leftTailSubset(a, c)
                    leftTailSubset(b, c)
                    mergeSubsetPreservation(at, bt, c)
                    val atmbt = at.merge(bt)
                    assert(c.contains(ah))
                    assert(ret == Cons(ah, atmbt))
                    subsetContainAll(atmbt, c)
                    assert(ret.forall(k=>c.contains(k)))
                    forallContainsSubset(ret, c)
                    assert(ret.isSubsetOf(c))
                } else if (ah < bh) {
                    leftTailSubset(a, c)
                    mergeSubsetPreservation(at, b, c)
                    assert(ret == Cons(ah, at.merge(b)))
                    subsetContainAll(at.merge(b), c)
                    assert(c.contains(ah))
                    forallContainsSubset(ret, c)
                    assert(ret.isSubsetOf(c))
                } else {
                    leftTailSubset(b, c)
                    mergeSubsetPreservation(a, bt, c)
                    assert(ret == Cons(bh, a.merge(bt)))
                    subsetContainAll(a.merge(bt), c)
                    assert(c.contains(bh))
                    forallContainsSubset(ret, c)
                    assert(ret.isSubsetOf(c))
                }
            }
        }
     }.ensuring(a.merge(b).isSubsetOf(c))

    def leftTailSubset(l1: SortedList, l2: SortedList) : Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1 != Nil)
        require(l1.isSubsetOf(l2))

        assert(l2 != Nil)
        (l1, l2) match {
            case (Cons(x, xs), Cons(y, ys)) => {
                if (xs.isSubsetOf(ys)) {
                    if (xs != Nil) {
                        leftTailSubset(xs, ys)
                    } else ()
                } else {
                    leftTailSubset(l1, ys)
                }
            }
        }
    }.ensuring(l1.tail.isSubsetOf(l2))

    def remImpliesSubset(l:SortedList, e: Int) : Unit = {
        require(l.isValid)
        subsetReflexivity(l)
        l match{
            case Nil => {
                assert(l.remove(e).isSubsetOf(l))
            }
            case Cons(x, xs) if (x == e) => {
                leftTailSubset(l, l)
                assert(xs.isSubsetOf(l))
                assert(l.remove(e).isSubsetOf(l))
            }
            case Cons(x, xs) if (x != e) => {
                leftTailSubset(l, l)
                remImpliesSubset(xs, e)
            }
        }
    }.ensuring(l.remove(e).isSubsetOf(l))

    def subsetTransitivity(l1:SortedList, l2:SortedList, l3:SortedList): Unit = {
        require(l1.isValid && l2.isValid && l3.isValid)
        require(l1.isSubsetOf(l2))
        require(l2.isSubsetOf(l3))
        if (l1 != Nil) {
            if (l1.isSubsetOf(l2.tail)) {
                leftTailSubset(l1, l2)
                strongTailsSubset(l2, l3)
                subsetTransitivity(l1, l2.tail, l3.tail)
            } else if (l2.isSubsetOf(l3.tail)) {
                subsetTransitivity(l1, l2, l3.tail)
            } else {
                strongTailsSubset(l1, l2)
                strongTailsSubset(l2, l3)
                subsetTransitivity(l1.tail, l2.tail, l3.tail)
            }
        }
    }.ensuring(l1.isSubsetOf(l3))

    def subsetAntisymmetry(s1:SortedList, s2:SortedList): Unit = {
        require(s1.isValid)
        require(s2.isValid)
        require(s1.isSubsetOf(s2))
        require(s2.isSubsetOf(s1))
        (s1,s2) match {
            case (Nil, _) => assert( s2==Nil)
            case (_,Nil) => assert(s1==Nil)
            case (Cons(x,xs),Cons(y,ys)) => {
                assert(x==y)
                subsetAntisymmetry(xs,ys)
            }
        }
    }.ensuring(s1.set_equals(s2))

    def removeAllImpliesSubset(l:SortedList, from:SortedList): Unit = {
        require(l.isValid)
        require(from.isValid)

        from match {
            case Nil => subsetReflexivity(l)
            case Cons(x, xs) => {
                val mid = l.remove(x)
                val ret = l.removeAll(from)

                remImpliesSubset(l, x)
                assert(mid.isSubsetOf(l)) // lem1

                removeAllImpliesSubset(mid, xs)
                // mid.removeAll(xs).isSubset(mid) // lem2

                // we want mid.removeAll(xs).isSubsetOf(l)
                // so we need lem1 and lem2 and transitivity
                subsetTransitivity(mid.removeAll(xs), mid, l)

                assert(mid.removeAll(xs) == ret)
            }
        }
    }.ensuring(l.removeAll(from).isSubsetOf(l))

    def remDiffElemPreservesContains(l:SortedList,e1:Int,e2:Int):Unit={
        require(l.isValid)
        require(e1!=e2)
        val remd = l.remove(e2)
        if(!l.contains(e1)) then{
            ncImplremoveNc(l,e1,e2)
        }
        else{
            assert(l.contains(e1))
            l match{
                case Nil => {}
                case Cons(x,xs) => {
                    if x==e1 then{
                        assert(l.contains(e1))
                        if e1 < e2 then {
                            assert(remd.head == x)
                            assert(remd.contains(e1))
                        }
                        else{
                            assert(e1>e2)
                            vsosaImplNotContain(l,e2)
                            assert(!l.contains(e2))
                            ncImplremoveNc(l,e2,e2)
                        }
                    }
                    else if (x < e1) then{
                        remDiffElemPreservesContains(xs,e1,e2)
                    }
                    else{
                        vsosaImplNotContain(l,e1)
                        assert(false)
                    }
                }
            }
        }

    }.ensuring(l.contains(e1) == l.remove(e2).contains(e1))

    @library
    def removeMoreSubsetOfRemoveLess(l1:SortedList,l2:SortedList,x:Int): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(Cons(x,l2).isValid)
        assert(!l2.contains(x))
    }.ensuring(l1.removeAll(Cons(x,l2)).isSubsetOf(l1.removeAll(l2)))

    // def remSuperSetImpliesNotContainSubset(l:SortedList,subset:SortedList,superset: SortedList): Unit = {
    //     //This could also have been called "removeAll is an invariant wrt subset"
    //     require(l.isValid)
    //     require(subset.isValid)
    //     require(superset.isValid)
    //     require(subset.isSubsetOf(superset)) // subset <= superset
    //     decreases(l.size())
    
    //     val rsuper = l.removeAll(superset)
    //     val rsub   = l.removeAll(subset)
    //     removeAllImpliesSubset(l,superset)
    //     removeAllImpliesSubset(l,subset)
    //     superset match
    //         case vp.Cons(x, xs) =>{
    //             remImpliesSubset(l,x)
    //             assert(!rsuper.contains(x))
    //             removeMoreSubsetOfRemoveLess(l,xs,x)
    //             // if subset.contains(x) then{

    //             //     assert(!rsub.contains(x))
    //             //     zremSuperSetImpliesNotContainSubset(l.remove(x),subset.remove(x),xs)
    //             // }
    //             // else{
    //             //     if l.contains(x) then assert(rsub.contains(x))
    //             // }
    //         }
    //         case vp.Nil => {
    //             assert(subset == vp.Nil)
    //             assert(rsub == rsuper)
    //             subsetReflexivity(l)
    //         }
        
    // }.ensuring(l.removeAll(superset).isSubsetOf(l.removeAll(subset)))

    def remdAllSubsetOfRemHead(l1:SortedList,l2:SortedList,l3:SortedList,h:Int): Unit ={
        // If somehow l1.removeAll(l2) is a subset of some list l3
        // then l1.removeAll(Cons(h,l2)) is a subset of some list l3
        require(l1.isValid)
        require(l2.isValid)
        require(l3.isValid)
        require(Cons(h,l2).isValid)
        require(l1.removeAll(l2).isSubsetOf(l3))

        removeMoreSubsetOfRemoveLess(l1,l2,h)
        subsetTransitivity(l1.removeAll(Cons(h,l2)),l1.removeAll(l2),l3)
    }.ensuring(l1.removeAll(Cons(h,l2)).isSubsetOf(l3))


    def forAllContainsSelf(l: SortedList): Unit = {
        require(l.isValid)
        subsetReflexivity(l)
        l match {
            case Nil => {
                assert(l.forall(k => l.contains(k)))
            }
            case Cons(x, xs) => {
                forAllContainsSelf(xs)
                subsetContainAll(xs,l)
                assert(xs.forall(k=>xs.contains(k)))
                assert(l.contains(x))
                assert(l.forall(k => l.contains(k)))
            }
        }
    }.ensuring(l.forall(k => l.contains(k)))

    def tailSubsetOfSelf(l1:SortedList): Unit ={
        require(l1.isValid)
        require(l1!=Nil)
        l1 match{
            case Cons(x,Nil)=>{}
            case Cons(x,xs) => {
                tailSubsetOfSelf(xs)
            }
        }
    }.ensuring(l1.tail.isSubsetOf(l1))

    def mergeCommutativity(l1:SortedList,l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)

        val lhs = l1.merge(l2)
        val rhs = l2.merge(l1)

        (l1,l2) match {
            case (Nil,_) => {
                assert(lhs == l2)
                assert(rhs == l2)
                assert(l1.merge(l2) == l2.merge(l1))
            }
            case (_,Nil) => {
                assert(lhs == l1)
                assert(rhs == l1)
                assert(l1.merge(l2) == l2.merge(l1))
            }
            case (Cons(x,xs),Cons(y,ys)) => {
                if x == y then {
                    assert(lhs == Cons(x,xs.merge(ys)))
                    assert(rhs == Cons(y,ys.merge(xs)))
                    mergeCommutativity(xs,ys)
                    assert(xs.merge(ys) == ys.merge(xs))
                    assert(Cons(x,xs.merge(ys)) ==  Cons(y,ys.merge(xs)))
                    assert(lhs == rhs)
                }
                else if (x < y) then {
                    assert(lhs == Cons(x,xs.merge(l2)))
                    assert(rhs == Cons(x,l2.merge(xs)))
                    mergeCommutativity(xs,l2)
                    assert(xs.merge(l2) == l2.merge(xs))
                    assert(Cons(x,xs.merge(l2)) ==  Cons(x,l2.merge(xs)))
                    assert(lhs == rhs)
                }
                else {
                    assert(lhs == Cons(y,l1.merge(ys)))
                    assert(rhs == Cons(y,ys.merge(l1)))
                    mergeCommutativity(l1,ys)
                    assert(l1.merge(ys) == ys.merge(l1))
                    assert(Cons(y,l1.merge(ys)) ==  Cons(y,ys.merge(l1)))
                    assert(lhs == rhs)
                }
            }
        }
    }.ensuring(l1.merge(l2) == l2.merge(l1))

    def eSmallerHeadAndMergedImplSmallerThanHead(e:Int,l1:SortedList,l2: SortedList): Unit={
        require(l1.isValid)
        require(l2.isValid)
        require(l1!=Nil)
        require(l2!=Nil)
        require(e<l1.head)
        require(e<l2.head)
    }.ensuring(e < l1.merge(l2).head)

    def mergeOneSmallerPreservesSubset(l1:SortedList,l2: SortedList,e:Int): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.isSubsetOf(l2))
        require(l1!=Nil)
        require(l2!=Nil)
        require(e<l2.head)
        mergeCommutativity(l2,Cons(e,Nil))
        tailSubsetOfSelf(Cons(e,Nil).merge(l2))
        assert(l2.isSubsetOf(Cons(e,Nil).merge(l2)))
        subsetTransitivity(l1,l2,Cons(e,Nil).merge(l2))
        assert(l1.isSubsetOf(Cons(e,Nil).merge(l2)))
        assert(l1.isSubsetOf(l2.merge(Cons(e,Nil))))
    }.ensuring(l1.isSubsetOf(l2.merge(Cons(e,Nil))))

    def mergeOnePreservesSubset(l1:SortedList,l2: SortedList,e:Int): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.isSubsetOf(l2))
        l1 match{
            case Nil => {}
            case Cons(x,xs) =>{
                l2 match{
                    case Nil => assert(l1 == Nil)
                    case Cons(y,ys) =>{
                        if e<y then mergeOneSmallerPreservesSubset(l1,l2,e)
                        else if y==e then {
                            
                        }
                        else{
                            assert(y<e)
                            val mrgd = l2.merge(Cons(e,Nil))
                            assert(mrgd.head == y)
                            if y == x then {
                                if(xs == Nil) then {}
                                else{
                                    assert(mrgd.head == x)
                                    mergeOnePreservesSubset(xs,ys,e)
                                    assert(xs.isSubsetOf(l2.tail.merge(Cons(e,Nil))))
                                    eSmallerHeadAndMergedImplSmallerThanHead(y,l2.tail,Cons(e,Nil))
                                    mergeOneSmallerPreservesSubset(xs,l2.tail.merge(Cons(e,Nil)),y)  
                                }
                            }
                            else{
                                //simply go right :)
                                mergeOnePreservesSubset(l1,ys,e)
                                assert(l1.isSubsetOf(l2.tail.merge(Cons(e,Nil))))
                                eSmallerHeadAndMergedImplSmallerThanHead(y,l2.tail,Cons(e,Nil))
                                mergeOneSmallerPreservesSubset(l1,l2.tail.merge(Cons(e,Nil)),y)
                            }
                        }
                    }
                }
            }
        }
    }.ensuring(l1.isSubsetOf(l2.merge(Cons(e,Nil))))

    def mergeOneImplContains(l1:SortedList,e:Int):Unit = {
        require(l1.isValid)
        l1 match{
            case Nil => {
                assert(l1.merge(Cons(e,Nil)) == Cons(e,Nil))
            }
            case Cons(x,xs) => {
                if (x == e) then {}
                else mergeOneImplContains(xs,e)
            }
        }
    }.ensuring(l1.merge(Cons(e,Nil)).contains(e))

    def mergeLeftRightPreservesSubsetTrivial(l: SortedList,e:Int): Unit={
        require(l.isValid)
        val cons = Cons(e,Nil)
        val mrg = l.merge(cons)
        l match{
            case Nil => {
                assert(mrg == cons)
                subsetReflexivity(cons)
            }
            case Cons(x,xs) => {
                if x == e then {
                    assert(mrg == l)
                    assert(l.contains(e))
                }
                else{
                    mergeLeftRightPreservesSubsetTrivial(xs,e)
                }
            }
        }
    }.ensuring(Cons(e,Nil).isSubsetOf(l.merge(Cons(e,Nil))))


    def mergeLeftRightPreservesSubset(l1:SortedList,l2: SortedList,e:Int): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.isSubsetOf(l2))
        mergeOnePreservesSubset(l1,l2,e)
        assert(l1.isSubsetOf(l2.merge(Cons(e,Nil))))
        mergeLeftRightPreservesSubsetTrivial(l2,e)
        assert(Cons(e,Nil).isSubsetOf(l2.merge(Cons(e,Nil))))
        mergeSubsetPreservation(l1,Cons(e,Nil),l2.merge(Cons(e,Nil)))
    }.ensuring(l1.merge(Cons(e,Nil)).isSubsetOf(l2.merge(Cons(e,Nil))))

    def mergeDistributivityOne(l1:SortedList,l2: SortedList,l3:SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l3.isValid)
        decreases(l1.size()+l2.size()+l3.size())

        val lhs_1 = l1.merge(l2)
        val lhs_2 = lhs_1.merge(l3)

        val rhs_i = l2.merge(l3)
        val rhs_o = l1.merge(rhs_i)

        (l1,l2,l3) match {
            case (Nil,_,_) => {
                assert(lhs_1 == l2)
                assert(lhs_2 == l2.merge(l3))
                assert(rhs_i == l2.merge(l3))
                assert(rhs_o == l2.merge(l3))
                assert(lhs_2 == rhs_o)
            }
            case (_,Nil,_) => {
                assert(lhs_1 == l1)
                assert(lhs_2 == l1.merge(l3))
                assert(rhs_i == l3)
                assert(rhs_o == l1.merge(l3))
                assert(lhs_2 == rhs_o)
            }
            case (_,_,Nil) => {
                assert(lhs_2 == lhs_1)
                assert(rhs_i == l2)
                assert(rhs_o == l1.merge(l2))
                assert(lhs_1 == rhs_o)
                assert(lhs_2 == rhs_o)
            }
            case (Cons(x,xs), Cons(y,ys), Cons(z,zs)) => {
                if (x < y && x < z) {
                    assert(lhs_1 == Cons(x, xs.merge(l2)))
                    assert(lhs_2 == Cons(x, (xs.merge(l2)).merge(l3)))
                    assert(rhs_o == Cons(x, xs.merge(l2.merge(l3))))
                    mergeDistributivityOne(xs, l2, l3)
                    assert((xs.merge(l2)).merge(l3) == xs.merge(l2.merge(l3)))
                    assert(lhs_2 == rhs_o)
                }
                else if (y < x && y < z) {
                    assert(rhs_i == Cons(y, ys.merge(l3)))
                    assert(rhs_o == Cons(y, l1.merge(ys.merge(l3))))
                    assert(lhs_1 == Cons(y, l1.merge(ys)))
                    assert(lhs_2 == Cons(y, (l1.merge(ys)).merge(l3)))
                    mergeDistributivityOne(l1, ys, l3)
                    assert((l1.merge(ys)).merge(l3) == l1.merge(ys.merge(l3)))
                    assert(lhs_2 == rhs_o)
                }
                else if (z < x && z < y) {
                    assert(rhs_i == Cons(z, l2.merge(zs)))
                    assert(rhs_o == Cons(z, l1.merge(l2.merge(zs))))
                    assert(lhs_2 == Cons(z, l1.merge(l2).merge(zs)))
                    mergeDistributivityOne(l1, l2, zs)
                    assert((l1.merge(l2)).merge(zs) == l1.merge(l2.merge(zs)))
                    assert(lhs_2 == rhs_o)
                }
                else {
                    if (x == y && y == z) {
                        assert(lhs_1 == Cons(x, xs.merge(ys)))
                        assert(lhs_2 == Cons(x, (xs.merge(ys)).merge(zs)))
                        assert(rhs_i == Cons(y, ys.merge(zs)))
                        assert(rhs_o == Cons(x, xs.merge(ys.merge(zs))))
                        mergeDistributivityOne(xs, ys, zs)
                        assert((xs.merge(ys)).merge(zs) == xs.merge(ys.merge(zs)))
                        assert(lhs_2 == rhs_o)
                    }
                    else if (x == y) {
                        assert(lhs_1 == Cons(x, xs.merge(ys)))
                        assert(lhs_2 == Cons(x, (xs.merge(ys)).merge(l3)))
                        mergeDistributivityOne(xs, ys, l3)
                        assert((xs.merge(ys)).merge(l3) == xs.merge(ys.merge(l3)))
                        assert(lhs_2 == rhs_o)
                    }
                    else if (y == z) {
                        assert(rhs_i == Cons(y, ys.merge(zs)))
                        mergeDistributivityOne(l1, ys, zs)
                        assert(lhs_2 == rhs_o)
                    }
                    else {
                        assert(x == z)
                        mergeDistributivityOne(xs, l2, zs)
                        assert(lhs_2 == rhs_o)
                    }
                }
            }
        }
    }.ensuring(l1.merge(l2).merge(l3) == l1.merge(l2.merge(l3)))

    def mergeDistributivity(l1:SortedList,l2: SortedList,l3:SortedList): Unit = {
       // Generated with a Python script haha
       require(l1.isValid)
       require(l2.isValid)
       require(l3.isValid)
       mergeCommutativity(l1,l2)
       mergeCommutativity(l2,l3)
       mergeCommutativity(l1,l3)
       mergeDistributivityOne(l1,l2,l3)
       mergeDistributivityOne(l2,l3,l1)
       mergeDistributivityOne(l3,l1,l2)
       mergeDistributivityOne(l2,l1,l3)
       mergeDistributivityOne(l1,l3,l2)
       mergeDistributivityOne(l3,l2,l1)
   }.ensuring(
       l1.merge(l2).merge(l3) == l1.merge(l2.merge(l3)) &&
       l2.merge(l1).merge(l3) == l1.merge(l2.merge(l3)) &&
       l2.merge(l3).merge(l1) == l2.merge(l3.merge(l1)) &&
       l1.merge(l3).merge(l2) == l1.merge(l3.merge(l2)) &&
       l3.merge(l1).merge(l2) == l3.merge(l1.merge(l2)) &&
       l3.merge(l2).merge(l1) == l3.merge(l2.merge(l1))
   )


    // def tailMergeSubOfParentMerge(l1:SortedList,l2: SortedList): Unit = {
    //     require(l1.isValid)
    //     require(l2.isValid)
    //     require(l1!=Nil)
    //     require(l2!=Nil)
    //     //require(l1.tail.isSubsetOf(l1.tail.merge(l2.tail)))
    //     tailSubsetOfSelf(l1)
    //     assert(l1.tail.isSubsetOf(l1))
    //     tailSubsetOfSelf(l2)
    //     assert(l2.tail.isSubsetOf(l2))

    //     assert(l1.tail.isSubsetOf(l1.merge(l2)))
    //     assert(l2.tail.isSubsetOf(l1.merge(l2)))
    //     mergeSubsetPreservation(l1.tail,l2.tail,l1.merge(l2))
    // }.ensuring(l1.tail.merge(l2.tail).isSubsetOf(l1.merge(l2)))

    def alwaysSubsetOfMerged(l1:SortedList,l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        decreases(l1.merge(l2).size())
        mergeCommutativity(l1,l2)
        (l1,l1.merge(l2)) match {
            case (Nil, _) => {}
            case (Cons(x, xs), Nil) => assert(false)
            case (Cons(x, xs), Cons(y, ys)) => {
                assert(ys.isSubsetOf(l2))
                if (x == y) {
                    mergeDistributivity(l1,l2,xs)
                    mergeDistributivity(l1,l2,xs)
                    alwaysSubsetOfMerged(xs,ys)
                    assert(xs.isSubsetOf(xs.merge(ys))) //  ==== xs <= xs U ys
                    // we need 
                    // 1) xs U ys <= l1 U l2
                    // 2) xs+head = l1
                    // 3) a <= b U c ==> a+e <= (bUC)+e 
                } else if (x < y) {
                    assert(false)
                } else {
                    alwaysSubsetOfMerged(l1,ys)
                    assert(l1.isSubsetOf(l1.merge(ys))) //  ===== l1 <= l1 U ys
                    //val smallMerge = y.merge()
                    // we need :
                    // 1) a U b <= a U (b+e) 

                    subsetTransitivity(l1,l1.merge(ys),l1.merge(l2))
                }
            }
        }

    }.ensuring(l1.isSubsetOf(l1.merge(l2)))

    def mergeImplForAllContains(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        decreases(l1.size()+l2.size())
        //alwaysSubsetOfMerged(l1,l2)
        subsetContainAll(l1,l1.merge(l2))
    }.ensuring(l1.forall(k => l1.merge(l2).contains(k)))

    def forallPredSubst(l:SortedList,p:Int=>Boolean) : Unit = {
        require(l.isValid)
        require(l != Nil)
    }.ensuring(l.forall(p) == (p(l.head) && l.tail.forall(p)))

    def containsImplBiggerThanHead(l:SortedList,e:Int): Unit = {
        require(l.isValid)
        require(l.contains(e))

        l match {
            case Nil => assert(false)
            case Cons(x,Nil) => assert(x==e)
            case Cons(x,xs) => {
                if x==e then assert(true)
                else {
                    assert(xs.contains(e))
                    assert(xs.isValid)
                    containsImplBiggerThanHead(xs,e)
                }
            }
        }
    }.ensuring(e >= l.head)

    def mergeContainingElementIsNOP(l:SortedList,e:Int): Unit = {
        require(l.isValid)
        require(l.contains(e))
        containsImplBiggerThanHead(l,e)
        l match{
            case Cons(x,Nil) => {
                assert(x == e)
                assert(Cons(x,Nil).merge(l) == l)
            }
            case Cons(x,xs) => {
                if x == e then {
                    assert(Cons(e,Nil).merge(l) == Cons(x,xs))
                    assert(Cons(e,xs) == l)
                }
                else if x < e then{
                    assert(Cons(e,Nil).merge(l) == Cons(x,Cons(e,Nil).merge(xs)))
                    mergeContainingElementIsNOP(xs,e)
                    assert(Cons(e,Nil).merge(xs) == xs)
                    assert(Cons(e,Nil).merge(l) == Cons(x,xs))
                    assert(Cons(e,Nil).merge(l) == l)
                }
                else{
                    assert(false)
                }
            }
        }
    }.ensuring(Cons(e,Nil).merge(l) == l)

    def mergeHeadPreservation(l1:SortedList,l2:SortedList) : Unit = {
        require(l1.isValid)
        require(l1!=Nil)
        require(l2.isValid)
        require(l2.contains(l1.head))
        decreases(l2.size())
        assert(l2!=Nil)
        containsImplBiggerThanHead(l2,l1.head)
        (l1,l2) match {
            case (Cons(x,Nil),_) =>{
                assert(l1.tail.merge(l2) == l2)
                mergeContainingElementIsNOP(l2,x)
                assert(l1.merge(l2) == l2)
            } 
            case (Cons(x,xs),Cons(y,ys)) => {
                if x == y then {
                    assert(l1.merge(l2) == Cons(x,xs.merge(ys)))
                    assert(y<xs.head)
                    assert(l1.tail.merge(l2) == Cons(y,xs.merge(ys)))
                }
                else{
                    if x < y then{
                        assert(false) // because of contains, proven by containsImplBiggerThanHead(l2,l1.head)
                    }
                    else{
                        assert(ys.contains(x))
                        assert(l1.merge(l2) == Cons(y,l1.merge(ys)))
                        mergeHeadPreservation(l1,ys)
                        assert(l1.tail.merge(ys) == l1.merge(ys))
                        assert(l1.merge(l2) == Cons(y,l1.tail.merge(ys)))
                        assert(l1.tail.merge(l2) == Cons(y,l1.tail.merge(ys)))
                    }
                }
            }
        }
    }.ensuring(l1.tail.merge(l2) == l1.merge(l2))

    @library
    def forAllNameSubstitution(l1:SortedList,l2:SortedList,l3:SortedList): Unit ={
        //We have not managed to prove the Cons(x,xs) case of the match this as it -- we would need some sort of stainless annotation
        // to be able to tell stainless to treat lambda equality as function proofs
        require(l1.isValid)
        require(l2.isValid)
        require(l3 == l1.merge(l2))
        require(l1.forall(k => l1.merge(l2).contains(k)))

        val start_predicate = k => l1.merge(l2).contains(k)
        val ret_predicate = k => l3.contains(k)

        l1 match{
            case Nil => {}
            case Cons(x,Nil) =>{
                assert(l1.forall(ret_predicate) == ret_predicate(x))
                assert(l1.forall(start_predicate) == start_predicate(x))
                assert(ret_predicate(x) == l3.contains(x))
                assert(start_predicate(x) == l1.merge(l2).contains(x))
            }
            case Cons(x,xs) => {
                assert(xs == l1.tail)
                forallPredSubst(l1,ret_predicate)
                assert(l1.forall(ret_predicate) == (ret_predicate(x) && xs.forall(ret_predicate)))
                forallPredSubst(l1,start_predicate)
                assert(l1.forall(start_predicate) == (start_predicate(x) && xs.forall(start_predicate)))
                
                assert(ret_predicate(x) == l3.contains(x))
                assert(start_predicate(x) == l1.merge(l2).contains(x))
                
                if l2.contains(x) then{
                    // In general, we cannot deduce that l.tail.forall(p) ==> l.forall(p)
                    //However, when p == the "contains all elements from another list" predicate, this becomes obvious thanks to mergeHeadPreservation
                    mergeHeadPreservation(l1,l2)
                    assert(xs.merge(l2) == l1.merge(l2))
                    assert(xs.merge(l2) == l3)
                    leftTailForallHolds(xs,start_predicate)
                    assert(xs.forall(start_predicate))
                    assert(xs.forall(k => l1.merge(l2).contains(k)))
                    leftTailForallContains(xs,l1.merge(l2))
                    forAllNameSubstitution(xs,l2,l3)
                    assert(xs.forall(ret_predicate))
                    assert(l1.forall(ret_predicate))
                }
                else{
                    l2 match{
                        case Nil => {
                            assert(l1.merge(l2) == l1)
                            val simplified_start_pred = k => l1.contains(k)
                            //The following 
                            assert(start_predicate == simplified_start_pred)

                        }
                        case Cons(y,ys) => {
                            //Now we need  xs.forall(next_start_predicate)  IMPLIES  l1.forall(start_predicate)
                            //This is basically the `right` equivalent of `leftTail leftTailForallContains (modulo "predicate simplification", which must also somehow be proven), 
                            
                        }
                    }
                }
            }
        }
    }.ensuring(l1.forall(k => l3.contains(k)))

    def mergePreserveSubset(l1:SortedList,l2:SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        mergeImplForAllContains(l1,l2)
        assert(l1.forall(k => l1.merge(l2).contains(k)))
        val l3 = l1.merge(l2)
        forAllNameSubstitution(l1,l2,l3)
        assert(l1.forall(k => l3.contains(k)))
        forallContainsSubset(l1,l3)
    }.ensuring(l1.isSubsetOf(l1.merge(l2)))

    // def zzzzzzremAllSubsetOfRem(l:SortedList,e:Int,l2:SortedList): Unit ={
    //     require(l.isValid)
    //     require(l2.isValid)
    //     require(l2.contains(e))
    //     decreases(l2)
    //     l2 match{
    //         case Cons(x,Nil) => {
    //             assert(x==e)
    //             assert(l.removeAll(l2) == l.remove(x))
    //             subsetReflexivity(l)
    //         }
    //         case Cons(x,xs) => {
    //             if x==e then {
    //                 assert(!xs.contains(e))

    //             }
    //             else{
    //                 zzzzzzremAllSubsetOfRem(l,e,xs)
    //             }
    //         }
    //     }
    // }.ensuring(l.removeAll(l2).isSubsetOf(l.remove(e)))

    // def zzzzzcontDepsRemovedFromListRec(l:SortedList,e:Int,l2:SortedList): Unit ={
    //     require(l.isValid)
    //     require(l2.isValid)
    //     require(l.contains(e))
    //     require(l2.contains(e))
    //     decreases(l2.size())

    //     assert(l2!=Nil)
    //     l2 match{
    //         case Cons(x,Nil) => {
    //             assert(x==e)
    //             assert(l.removeAll(l2) == l.remove(x))
    //             removedImpliesDoesNotContain(l,e)
    //             assert(!l.removeAll(l2).contains(e))
    //         }
    //         case Cons(x,xs) => {
    //             val lhead = l.remove(x)
    //             if(x!=e){
    //                 remDiffElemPreservesContains(l,e,x)
    //                 assert(lhead.contains(e))
    //                 assert(l.removeAll(l2).isSubsetOf(lhead))
    //                 zzzzzcontDepsRemovedFromListRec(l,e,xs)
    //             }
    //             else{
                    
    //             }
    //         }
    //     }
    // }.ensuring(!l.removeAll(l2).contains(e))

    // def zzzzcontDepsRemovedFromList(l:SortedList,e:Int,l2:SortedList):Unit = {
    //     require(l.isValid)
    //     require(l2.isValid)
    //     require(l.contains(e))
    //     l2 match{
    //         case Nil=>{
    //             assert(!l2.contains(e))
    //             assert(l.removeAll(l2) == l)
    //             assert(l.removeAll(l2).contains(e))
    //         }
    //         case Cons(x,xs) =>{
    //             if l2.contains(e) then{
    //                 assert(!l.removeAll(l2).contains(e))
    //             }
    //             else{
    //                 assert(l.removeAll(l2).contains(e))
    //             }  
    //         }
    //     }
    // }.ensuring(l.removeAll(l2).contains(e) == !l2.contains(e))

    // def zzzremAllPreservesContains(l:SortedList,e:Int,l2:SortedList): Unit = {
    //     require(l.isValid)
    //     require(l2.isValid)
    //     require(!l.contains(e))

    //     decreases(l2.size())
    //     assert(l.remove(e).removeAll(l2) == l.removeAll(Cons(e,l2)))
    //     ncImplremoveNc(l,e,e)
    //     assert(!l.remove(e).contains(e))
    //     l2 match{
    //         case Nil => {}
    //         case Cons(x,xs) =>{
    //             if x == e then {
    //                 assert(!l.remove(x).contains(e))
    //                 zzzremAllPreservesContains(l,e,xs)
    //             }
    //             else if e<x then{
    //                 vsosaImplNotContain(l2,e)
    //                 assert(!l2.contains(e))
    //                 remDiffElemPreservesContains(l,e,x)
    //                 assert(l.contains(e) == l.remove(x).contains(e))
    //                 assert(!l.remove(x).contains(e))
    //                 zzzremAllPreservesContains(l,e,xs)
    //             }
    //             else{
    //                 assert(!l.remove(x).contains(e))
    //                 zzzremAllPreservesContains(l,e,xs)
    //             }
    //         }
    //     }
    // }.ensuring(!l.removeAll(Cons(e,l2)).contains(e))

    // def zzremAllImpliesNCHead(l:SortedList,l2:SortedList): Unit = {
    //     require(l.isValid)
    //     require(l2.isValid)
    //     require(l2 != Nil)
    //     val ret = l.removeAll(l2)
    //     l2 match {
    //         case vp.Cons(x,xs) =>{
    //             if(!l.contains(x)) then assert(!ret.contains(x))
    //             else assert(!ret.contains(x))
    //         }
    //     }
    // }.ensuring(!l.removeAll(l2).contains(l2.head))

    

    // def removeAllImpliesNotExistContain(data_to_remove: SortedList,removed_from_list: SortedList): Unit = {
    //     require(data_to_remove.isValid)
    //     require(removed_from_list.isValid)
    //     data_to_remove match
    //         case vp.Nil => 
    //         case vp.Cons(x, xs) =>{
    //             removedImpliesDoesNotContain(removed_from_list,x)
    //             val ro = removed_from_list.remove(x)
    //             assert(removed_from_list.removeAll(Cons(x,Nil)) == ro)
    //             assert(!removed_from_list.removeAll(data_to_remove).exists(k=>ro.contains(k)))
    //             removeAllImpliesNotExistContain(xs,removed_from_list.remove(x))
    //         } 
        
    // }.ensuring(!data_to_remove.exists(k=>removed_from_list.removeAll(data_to_remove).contains(k)))
}
