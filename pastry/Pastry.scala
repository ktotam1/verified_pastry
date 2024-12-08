package pastry
import pastryMath.*
import stainless.collection.*
import java.util.HashMap
import stainless.lang.*
import sorted.*



case class Node(id: Int, replicationFactor: Int) {
    var network = Network()
    val routingTable: RoutingTable = RoutingTable(id)
    var leftLeafSet: LeafSet = LeafSet(id, true)
    var rightLeafSet: LeafSet = LeafSet(id, false)
    var neighbourhood: List[Int] = List() //incase i need it 
    
    def snoop(message: Message): Unit = {
        message match
            case Join(newId) => 
                neighbourhood = newId :: neighbourhood
                //println(s"$id is snooping join of $newId")
                handleJoin(newId)
                def foreach(l: List[Int]): Unit = {
                    l match
                        case x :: xs => network.send(JoinNotice(newId), newId, x)
                        case stainless.collection.Nil() => 
                }
                foreach((leftLeafSet.toList ++ rightLeafSet.toList).unique)
            case _ =>
    }
    // if you already know who it's going to 
    def send(message: Message, key: Int, to: Int): Unit = {
        //snoop if message is a join and send them our tables
        snoop(message)
        if to == id then 
            handleMessage(message) 
        else 
            network.send(message, key, to)
    }

    //if you need to figure out who its going to 
    def route(message: Message, key: Int): Boolean = {
        //println(s"${this.id} routed message")
        val id = routingTable.biggestMatchingPrefix(key)
        if id == -1 then 
            false 
        else 
            send(message, key, id) 
            true
    }

    //network gives you a message
    def receive(message: Message, key: Int): Unit = {
        snoop(message)
        //println(s"${this.id} is receiving $message")
        if (leftLeafSet.size()==0 || rightLeafSet.size()==0) ||
         leftSmaller(leftLeafSet.head, key, id) 
         && rightSmaller(key, rightLeafSet.last,id) then
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
            else 
                //println(s"${this.id} is forwarding message to $handler")
                send(message, key, handler)
        else 
            if !route(message, key) then 
                //println(s"${this.id} failed to route; spamming neighbors")
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
        //println(s"${id} is handling message ${msg}")
        msg match {
            case Join(id) => handleJoin(id)
            case JoinNotice(newId) => handleJoin(id)
            case Error(reason) => ////println(reason)
            case RoutingTableState(routingTable) =>
                this.routingTable.add(routingTable.id)
                this.routingTable.update(routingTable)
            case LeafSetState(leafSet, id) => 
                addToLeafSet(id)
                updateLeafSet(leafSet)
        }
    }



    private def handleJoin(newId: Int): Unit = {
        neighbourhood = newId :: neighbourhood
        routingTable.add(newId)
        addToLeafSet(newId)
        send(RoutingTableState(this.routingTable), newId, newId)
        send(LeafSetState(leftLeafSet.toList++rightLeafSet.toList, id), newId, newId)   
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
            if this.id==1 then println(stepsLeft(this.id, id) + " " + stepsRight(this.id, id))
            if stepsLeft(this.id, id) < stepsRight(this.id, id) then
                leftLeafSet.insert(id)
                if leftLeafSet.size().toInt > replicationFactor then 
                    leftLeafSet.drop(leftLeafSet.size().toInt -replicationFactor)
            else 
                rightLeafSet.insert(id)
                if rightLeafSet.size().toInt > replicationFactor then 
                    rightLeafSet.take(replicationFactor)
    }


    def mkSting(): String = {
        s"""
        ========================================
        Node: ${id}
        Left: ${leftLeafSet.toList}
        Right: ${rightLeafSet.toList}
        Route: ${routingTable.ids}
        Neigh: ${neighbourhood.unique}
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