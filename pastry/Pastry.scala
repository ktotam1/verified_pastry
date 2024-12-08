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
    var leftLeafSet: LeafSet = sorted.Nil
    leftLeafSet.isLeft = true
    leftLeafSet.id = id
    var rightLeafSet: LeafSet = sorted.Nil
    rightLeafSet.isLeft = false
    rightLeafSet.id = id
    var neighbourhood: List[Int] = List() //incase i need it 

    // if you already know who it's going to 
    def send(message: Message, key: Int, to: Int): Unit = {
        //snoop if message is a join and send them our tables
        message match
            case Join(newId) => 
                handleJoin(newId)
            case _ =>
        if to == id then 
            handleMessage(message) 
        else 
            network.send(message, key, to)
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
        println1(message.toString())
        if (leftLeafSet.size()==0 || rightLeafSet.size()==0) || leftLeafSet.head <= key && key <= rightLeafSet.last then
            def min(nodes: List[Int], nmin: Int, vmin: Int): Int = {
                nodes match 
                    case stainless.collection.Nil() => nmin
                    case x :: xs => 
                        if dist(x,key) < vmin then 
                            min(xs, x, dist(x,key))
                        else min(xs, nmin, vmin)
            }
            val handler = min(leftLeafSet.toList ++ rightLeafSet.toList, this.id, dist(key, this.id))
            if handler == id then 
                handleMessage(message) 
            else send(message, key, handler)
        else 
            if !route(message, key) then 
                def foreach(nodes: List[Int]): Unit = {
                    nodes match 
                        case x :: xs =>
                            if shl(x, key) > shl(id, key) && dist(x, key) < dist(id, key) then
                                send(message, key, x)
                            foreach(xs)
                        case _ =>
                }
                foreach(routingTable.idList() ++ leftLeafSet.toList ++ rightLeafSet.toList)
    }

    //we are definitely handling the message (deliver in Pastry ig)
    private def handleMessage(msg: Message): Unit = {
        println(s"${id} is handling message ${msg}")
        msg match {
            case Join(id) => handleJoin(id)
            case Error(reason) => println(reason)
            case RoutingTableState(routingTable) =>
                this.routingTable.update(routingTable)
            case LeafSetState(leafSet) => 
                updateLeafSet(leafSet)
        }
    }



    private def handleJoin(newId: Int): Unit = {
        routingTable.add(newId)
        addToLeafSet(newId)
        send(RoutingTableState(this.routingTable), newId, newId)
        send(LeafSetState(leftLeafSet.toList++rightLeafSet.toList), newId, newId)   
    }

    private def updateLeafSet(l: List[Int]): Unit = {
        l match 
            case x :: xs =>
                addToLeafSet(x)
                updateLeafSet(xs)
            case _ =>
    }

    private def addToLeafSet(id: Int): Unit = {
        if id != this.id then
            leftLeafSet = leftLeafSet.insert(id)
            if leftLeafSet.size().toInt > replicationFactor then 
                leftLeafSet = leftLeafSet.drop(leftLeafSet.size().toInt -replicationFactor)
            rightLeafSet = rightLeafSet.insert(id)
            if rightLeafSet.size().toInt > replicationFactor then 
                rightLeafSet = rightLeafSet.take(replicationFactor)
    }

    def println1(s: String)= {
        if id == 1 then println(s)
    }


    def mkSting(): String = {
        s"""
        ========================================
        Node: ${id}
        Left: ${leftLeafSet.toList}
        Right: ${rightLeafSet.toList}
        Route: ${routingTable.ids}
        ========================================
        """
    }
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