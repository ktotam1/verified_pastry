package pastry
import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

/**
    This file contains a decorator for a sorted List[Int], that contains only unique elements (hence, sorted Set)
    It describes a List that is always sorted in *ascending* order
    (i.e. smallest elements first)
*/
case class LeafSet(isLeft: Boolean, val cell: Cell[stainless.collection.List[Int]] = Cell(List()), var id: Int = 0)
 {  
    def setId(i: Int) = {
        this.id = i
    }

    def lt(x:Int,y:Int) =
        // println(s"""
        // id: ${id}
        // x: ${x} ${{stepsLeft(id, x)}}
        // y: ${y} ${{stepsLeft(id, y)}}
        // x < y: ${stepsLeft(id,x) > stepsLeft(id,y)}
        // """)
        if isLeft then 
            stepsLeft(id,x) > stepsLeft(id,y)
        else 
            stepsRight(id,x) < stepsRight(id,y)
    def size() : Int = {
        def counter(list: List[Int]): Int = {
            list match {
                case Nil() => 0
                case x :: xs => 1 + counter(xs)
            }
        }
        counter(cell.v)
    }

    def isSorted() : Boolean = {
        def sorted(l: List[Int]): Boolean = {
            l match 
                case Nil() => true
                case Cons(_,Nil()) => true
                case Cons(x1, Cons(x2, xs)) => lt(x1,x2) && sorted(Cons(x2,xs))
        }
        sorted(cell.v)
    }

    def content(): Set[Int] = cell.v.toSet

    def contains(e: Int) = {
        // require(size()!=0)
        content().contains(e)
    } 

    def toList: List[Int] = {
        cell.v
    }

    def head: Int = { 
        cell.v.head
    }
    
    def last: Int = {
        cell.v.last
    }

    def insert(e : Int): Unit = {
        require(isSorted())
        def inserter(list: List[Int]): List[Int] = {
            list match {
                case Nil() => Cons(e, Nil())
                case Cons(x, xs) if (x == e) => Cons(x,xs)
                case Cons(x, xs) if lt(x, e) => Cons(x, inserter(xs))
                case Cons(x, xs) if lt(e, x) => Cons(e, Cons(x,xs))
            }
        }
        cell.v = inserter(cell.v)
    }.ensuring {_ => isSorted() && content() == this.content() ++ Set(e)}
    
    def remove(e: Int) : Unit= {
        this.cell.v = this.cell.v.filter(_ != e)
    }
    def drop(i: Int): Unit = {
        def dropHelper(ls: List[Int], i: Int): List[Int] ={
            ls match 
                case Nil() => Nil()
                case Cons(x, xs) => if i > 0 then dropHelper(xs, i-1) else Cons(x, xs)
        }
        cell.v = dropHelper(cell.v, i)
    }

    def take(i: Int): Unit = {
        def takeHelper(ls: List[Int], i: Int): List[Int] = {
            ls match
                case Nil() => Nil()
                case Cons(x, xs) => if i > 0 then Cons(x, takeHelper(xs, i-1)) else Nil()
        }
        cell.v = takeHelper(cell.v, i)
    }
}
