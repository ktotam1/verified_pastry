
package pastry 
import stainless.collection.*
import stainless.lang.*
case class RoutingTable(id: Int,var ids: Map[Int, List[Int]] = Map()) {
    //MutableMap.withDefaultValue(() => List[Int]())
    //returns the KEY with the largest matching prefix. -1 otherwise
    def biggestMatchingPrefix(key: Int): Int = {
        val l = shl(id, key)
        def foreach(ids: List[Int], ans: Int , key: Int): Int = {
            ids match   
                case Nil() => key
                case x :: xs =>
                    if (shl(x,key) > ans) then
                        foreach(xs, shl(x,key),x)
                    else 
                        foreach(xs, ans, key)
        }
        foreach(ids(l), 0, -1)
    }
    def remove(id: Int): Unit = {
        ids = ids.updated(shl(id, this.id), ids(shl(id,this.id)).withFilter(_ != id))
    }
    def add(id: Int): Unit = {
        if id != this.id && !ids(shl(id, this.id)).contains(id) then
            ids = ids.updated(shl(id, this.id), id :: ids(shl(id,this.id)))
    }
    def update(other: RoutingTable): Unit = {
        val keys = ids.keys ++ other.ids.keys
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
        val keys = ids.keys
        def builder(keys: List[Int]): List[Int] = {
            keys match
                case stainless.collection.Nil() => stainless.collection.Nil()
                case x :: xs => ids(x) ++ builder(xs)
        }
        builder(keys)
    }

    
}