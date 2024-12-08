package pastry
import stainless.collection.*
import java.util.HashMap
import stainless.lang.*
import sorted.*

def abs(x: Int): Int = {
    if x < 0 then -x else x
}
def min(x: Int, y: Int): Int = {
    if x > y then y else x
}
def max(x: Int, y: Int): Int = {
    if x > y then x else y
}
def dist(x:Int, y:Int): Int = {
    min(abs(x-y), abs(max(x,y)-Int.MaxValue - min(x,y)))
}
//ring less than 
def rlt(x: Int,y: Int): Boolean = {
    if abs(x-y) < abs(max(x,y)-Int.MaxValue - min(x,y)) then 
        x < y
    else 
        x > y
}   

def shl(a: Int, b: Int): Int = {
        var i = 0
        var done = false 
        while(i <= 32 && !done) {
            if (a >> i == b >> i) 
                done = true 
            else 
                i += 1
        }
        32-i
}

case class RoutingTable(id: Int) {
    private var ids: MutableMap[Int, List[Int]] = MutableMap.withDefaultValue(() => List[Int]())
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
        ids.update(shl(id, this.id), id :: ids(shl(id,this.id)))
    }
    def update(other: RoutingTable): Unit = {
        val keys = List.fromScala((ids.theMap.keySet ++ other.ids.theMap.keySet).toList)
        def updater(keys: List[Int]): Unit = {
            keys match 
                case x :: xs => 
                    ids.update(x, ids(x) ++ other.ids(x))
                    updater(xs)
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

trait Message
case class Join(newId: Int) extends Message
case class Empty() extends Message
case class Msg(text: String) extends Message //for debugging purposes
case class requestState(requesterId: Int) extends Message
case class RoutingTableState(routingTable: RoutingTable) extends Message
case class LeafSetState(leafSet: List[Int]) extends Message
case class Error(reason: String) extends Message


case class Node(id: Int, replicationFactor: Int) {
    var network = Network()
    val routingTable: RoutingTable = RoutingTable(id)
    var leftLeafSet: SortedList = sorted.Nil
    var rightLeafSet: SortedList = sorted.Nil
    var neighbourhood: List[Int] = List() //incase i need it 
    // val neighbourHood = ?? 

    // if you already know who it's going to 
    def send(message: Message, key: Int, to: Int): Unit = {
        if to == id then handleMessage(message) else network.send(message, key, to)
    }

    //if you need to figure out who its going to 
    def route(message: Message, key: Int): Boolean = {
        val id = routingTable.biggestMatchingPrefix(key)
        if id == -1 then 
            false 
        else 
            send(message, key, id) 
            true
    }

    //network gives you a message
    def receive(message: Message, key: Int): Unit = {
        if leftLeafSet.head <= key && key <= rightLeafSet.last then
            def min(nodes: List[Int], nmin: Int, vmin: Int): Int = {
                nodes match 
                    case stainless.collection.Nil() => nmin
                    case x :: xs => 
                        if dist(x,key) < vmin then 
                            min(xs, x, dist(x,key))
                        else min(xs, nmin, vmin)
            }
            // val handler = min(leftLeafSet++rightLeafSet, this.id, dist(key, this.id))
            // if handler == id then handleMessage(message) else send(message, key, handler)
        else 
            if !route(message, key) then 
                def foreach(nodes: List[Int]): Unit = {
                    nodes match 
                        case x :: xs =>
                            if shl(x, key) > shl(id, key) && dist(x, key) < dist(id, key) then
                                send(message, key, x)
                            foreach(xs)
                }
                // foreach(routingTable.idList() ++ leftLeafSet ++ rightLeafSet)
    }

    //we are definitely handling the message (deliver in Pastry ig)
    private def handleMessage(msg: Message): Unit = {
        msg match {
            case Join(id) => handleJoin(id)
            case Error(reason) => println(reason)
        }
    }

    private def handleJoin(newId: Int): Unit = {
        send(RoutingTableState(this.routingTable), id, id)
    }

    //add
    // private def addToLeafSet(id: Int): Unit = {
    //     if rlt(id, this.id) then 
    //         leftLeafSet.insert(id)
    //         if leftLeafSet.length > replicationFactor then leftLeafSet.drop(leftLeafSet.length-replicationFactor)
    //     else 
    //         rightLeafSet.insert(id)
    //         if rightLeafSet.length < replicationFactor then rightLeafSet.take(replicationFactor)
    // }

    //remove a neighbor and search for a new one 
    // private def removeFromLeafSet(id: Int): Unit = {
        
    // }
}

class Network() { 
    var nodes: List[Node] = List()
    def add(node: Node) = {
        node.network = this //potential aliasing problem ? 
        nodes = node :: nodes
    }

    def send(msg: Message, key: Int, to: Int): Option[Error] = {
        def foreach(nodes: List[Node]): Option[Error] = {
            nodes match 
                case stainless.collection.Nil() => Option(Error(s"Node with ID ${to} not found"))
                case x :: xs => 
                    if x.id == to then
                        x.receive(msg, key) 
                        None()
                    else 
                        foreach(xs)
        }
        foreach(nodes)
    }
}