package pastry
import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

/**
    This file contains a decorator for a sorted List[Int], that contains only unique elements (hence, sorted Set)
    It describes a List that is always sorted in *ascending* order
    (i.e. smallest elements first)
*/
case class LeafSet(id: Int, isLeft: Boolean)
 {
    val cell: Cell[stainless.collection.List[Int]] = Cell(List())
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
                case x :: xs => 1 + counter(list)
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

    def drop(i: BigInt): Unit ={
        this.cell.v = cell.v.drop(i)
    }

    def take(i: BigInt): Unit = {
        this.cell.v = cell.v.take(i)
    }
}
