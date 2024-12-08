
package pastry 
import pastryMath.*
import stainless.collection.*
import java.util.HashMap
import stainless.lang.*
import sorted.*
case class RoutingTable(id: Int) {
    val ids: MutableMap[Int, List[Int]] = MutableMap.withDefaultValue(() => List[Int]())
    //returns the KEY with the largest matching prefix. -1 otherwise
    def biggestMatchingPrefix(key: Int): Int = {
        val l = shl(id, key)
        def foreach(ids: List[Int], ans: Int , key: Int): Int = {
            ids match   
                case stainless.collection.Nil() => key
                case x :: xs =>
                    if (shl(x,key) > ans) then
                        foreach(xs, shl(x,key),x)
                    else 
                        foreach(xs, ans, key)
        }
        foreach(ids(l), 0, -1)
    }
    def remove(id: Int): Unit = {
        ids.update(shl(id, this.id), ids(shl(id,this.id)).withFilter(_ != id))
    }
    def add(id: Int): Unit = {
        if id != this.id && !ids(shl(id, this.id)).contains(id) then
            ids.update(shl(id, this.id), id :: ids(shl(id,this.id)))
    }
    def update(other: RoutingTable): Unit = {
        val keys = List.fromScala((ids.theMap.keySet ++ other.ids.theMap.keySet).toList)
        def updater(keys: List[Int]): Unit = {
            keys match 
                case x :: xs => 
                    def foreach(ids: List[Int]): Unit = {
                        ids match
                            case id::rest => 
                                add(id)
                                foreach(rest)      
                            case _ =>
                    }
                    foreach(other.ids(x))
                    updater(xs)
                case _ => 
        }
        updater(keys)
    }
    def idList(): List[Int] = {
        val keys = List.fromScala(ids.theMap.keySet.toList)
        def builder(keys: List[Int]): List[Int] = {
            keys match
                case stainless.collection.Nil() => stainless.collection.Nil()
                case x :: xs => ids(x) ++ builder(xs)
        }
        builder(keys)
    }

    
}