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
        case Cons(i, t) => Set(i) ++ t.content()
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

    final def body: SortedList = {
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
            case (_, Nil) => false
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

    final def subsetSize(other: SortedList): BigInt = {
        0
    }
}
case object Nil extends SortedList
case class Cons(x: Int, tail: SortedList) extends SortedList


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

    def ncImplremoveNc(sl: SortedList, e:Int, k:Int): Unit = {
        require(sl.isValid)
        require(!sl.contains(e))
        require(k!=e)
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

    def reflexiveSub(l:SortedList): Unit = {
        require(l.isValid)
        l match {
            case Nil => ()
            case Cons(x, xs) => {
                assert(l.contains(x))
                reflexiveSub(xs)
            }
        }        
    }.ensuring(l.isSubsetOf(l))

    def strongTailsSubset(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.isSubsetOf(l2))
        require(l1 != Nil)
        require(l2 != Nil)
        if (l1.isSubsetOf(l2.body)) leftTailSubset(l1, l2.body)
    }.ensuring(l1.body.isSubsetOf(l2.body))


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
    }.ensuring(l1.body.forall(p))

    def leftTailForallContains(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1 != Nil)
        require(l1.forall(k=>l2.contains(k)))
        leftTailForallHolds(l1, k=>l2.contains(k))
    }.ensuring(l1.body.forall(k => l2.contains(k)))

    def headGreaterImplNotContains(l: SortedList, e: Int): Unit = {
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
    }.ensuring(l.body.contains(e))

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
    }.ensuring(l1.forall(k=>l2.body.contains(k)))

    def tailsForallContains(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1 != Nil)
        require(l2 != Nil)
        require(l1.forall(k=>l2.contains(k)))

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

    }.ensuring(l1.body.forall(k=>l2.body.contains(k)))

    def forallContainsSubset(l1: SortedList, l2: SortedList): Unit = {
        require(l1.isValid)
        require(l2.isValid)
        require(l1.forall(k => l2.contains(k)))
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
                    // at.merge(bt).isSubsetOf(c)
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
    }.ensuring(l1.body.isSubsetOf(l2))

    def remImpliesSubset(l:SortedList, e: Int) : Unit = {
        require(l.isValid)
        reflexiveSub(l)
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
            if (l1.isSubsetOf(l2.body)) {
                leftTailSubset(l1, l2)
                strongTailsSubset(l2, l3)
                subsetTransitivity(l1, l2.body, l3.body)
            } else if (l2.isSubsetOf(l3.body)) {
                subsetTransitivity(l1, l2, l3.body)
            } else {
                strongTailsSubset(l1, l2)
                strongTailsSubset(l2, l3)
                subsetTransitivity(l1.body, l2.body, l3.body)
            }
        }
    }.ensuring(l1.isSubsetOf(l3))

    def removeAllImpliesSubset(l:SortedList, from:SortedList): Unit = {
        require(l.isValid)
        require(from.isValid)

        from match {
            case Nil => reflexiveSub(l)
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

    // def remSuperSetImpliesNotContainSubset(l:SortedList,subset:SortedList,superset: SortedList): Unit = {
    //     require(l.isValid)
    //     require(subset.isValid)
    //     require(superset.isValid)
    //     require(subset.isSubsetOf(superset)) // subset <= superset
    
    //     val rsuper = l.removeAll(superset)
    //     val rsub   = l.removeAll(subset)
    //     superset match
    //         case vp.Cons(x, xs) =>{
    //             if subset.contains(x) then{
    //                 assert(!rsub.contains(x))
    //                 assert(!rsuper.contains(x))
    //                 remSuperSetImpliesNotContainSubset(l.remove(x),subset.remove(x),xs)
    //             }
    //             else{
    //                 if l.contains(x) then assert(rsub.contains(x))
    //             }
    //         }
    //         case vp.Nil => 
        
    // }.ensuring(l.removeAll(superset).isSubsetOf(l.removeAll(subset)))

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
