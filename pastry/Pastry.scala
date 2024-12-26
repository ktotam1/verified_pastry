package pastry
import stainless.collection.*
import stainless.lang.*
import stainless.io.StdOut.println
import stainless.io.State
import stainless.annotation.*

implicit val state: State = State(0)

case class Node(id: Int, replicationFactor: Int, 
                val network: Network, 
                var neighbourhood: List[Int] = List(), 
                val routingTable: Cell[RoutingTable] = Cell(RoutingTable()),
                val leftLeafSet: LeafSet = LeafSet(true),
                val rightLeafSet: LeafSet = LeafSet(false) ) {
    
    
    
    
    def init(): Unit= {
        routingTable.v.setId(id)
        leftLeafSet.setId(id)
        rightLeafSet.setId(id)
    }

    // def snoop(message: Message): Message = {
       
    // }
    // if you already know who it's going to 
    def forward(message: Message, key: Int, to: Int): Unit = {
        //snoop if message is a join and send them our tables
        val snooped =  message match
            case Join(newId, list) => 
                neighbourhood = newId :: neighbourhood
                //println(s"$id is snooping join of $newId")
                addNewId(newId)
                Join(newId, this.id :: list)
            case _ => freshen(message)
        if to == id then 
            handleMessage(message) 
        else 
            network.send(snooped, key, to)
    }

    //if you need to figure out who its going to 
    def route(message: Message, key: Int): Boolean = {
        val id = routingTable.v.biggestMatchingPrefix(key)
        if id == -1 then 
            false 
        else 
            // println(s"${this.id} routed message")
            forward(message, key, id) 
            true
    }

    //sending is actually the same as receiving oops 
    def send(message: Message, key: Int) = receive(message, key)
    
    //network gives you a message
    def receive(message: Message, key: Int): Unit = {
        val snooped =  message match
            case Join(newId, list) => 
                neighbourhood = newId :: neighbourhood
                //println(s"$id is snooping join of $newId")
                addNewId(newId)
                Join(newId, this.id :: list)
            case _ => freshen(message)
        // println(s"${this.id} is receiving $message with $key")
        if (leftLeafSet.size()==0 || rightLeafSet.size()==0) ||
         leftSmaller(leftLeafSet.head, key, id) || 
         rightSmaller(key, rightLeafSet.last,id) ||
         key == id then
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
                handleMessage(snooped) 
            else 
                // println(s"${this.id} is forwarding message to $handler")
                forward(snooped, key, handler)
        else 
            if !route(message, key) then 
                // println(s"${this.id} failed to route; spamming neighbors")
                def foreach(nodes: List[Int]): Unit = {
                    nodes match 
                        case x :: xs =>
                            if shl(x, key) > shl(id, key) && dist(x, key) < dist(id, key) then
                                forward(snooped, key, x)
                            foreach(xs)
                        case _ =>
                }
                foreach(routingTable.v.idList() ++ leftLeafSet.toList ++ rightLeafSet.toList)
    }   

    //we are definitely handling the message (deliver in Pastry ig)
    private def handleMessage(msg: Message): Unit = {
        // println(s"${id} is handling message ${msg}")
        msg match {
            case Join(newId, ls) => 
                addNewId(id)
                network.send(JoinReply(id, ls), newId, newId)
            case JoinNotice(newId) => addNewId(newId)
            case JoinReply(newId, path) => 
                def foreachPath(ids: List[Int]): Unit = {
                    ids match
                        case x :: xs => 
                            network.send(JoinNotice(this.id), x, x)
                            network.send(AskForState(this.id), x, x)
                            foreachPath(xs)
                        case Nil() => 
                }
                foreachPath(path)
                def foreachNotify(ids: List[Int]): Unit = {
                    ids match
                        case x :: xs => 
                            network.send(JoinNotice(this.id),x,x)
                            foreachNotify(xs)
                        case Nil() =>
                }
                foreachNotify(leftLeafSet.toList ++ rightLeafSet.toList ++ routingTable.v.idList())
            case AskForState(requesterId) => 
                network.send(RoutingTableState(this.routingTable.v), requesterId, requesterId)
                network.send(RoutingTableState(this.routingTable.v), requesterId, requesterId)
            // case Error(reason) => println(reason)
            case RoutingTableState(routingTable) =>
                this.routingTable.v.add(routingTable.id)
                this.routingTable.v.update(routingTable)
            case LeafSetState(leafSet, id) => 
                addToLeafSet(id)
                updateLeafSet(leafSet)
            case Msg(str, from) => 
                println(str)
        }
    }

    private def addNewId(newId: Int): Unit = {
        // println(s"${this.id} is adding id ${newId}")
        neighbourhood = newId :: neighbourhood
        routingTable.v.add(newId)
        addToLeafSet(newId)
        forward(RoutingTableState(this.routingTable.v), newId, newId)
        forward(LeafSetState(leftLeafSet.toList++rightLeafSet.toList, id), newId, newId)   
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

            leftLeafSet.insert(id)
            if leftLeafSet.size().toInt > replicationFactor then 
                leftLeafSet.drop(leftLeafSet.size().toInt -replicationFactor)
            rightLeafSet.insert(id)
            if rightLeafSet.size().toInt > replicationFactor then 
                rightLeafSet.take(replicationFactor)
    }


    def mkSting(): String = {
        "i guess not"
        // s"""========================================
        // Node: ${id}
        // Left: ${leftLeafSet.toList}
        // Right: ${rightLeafSet.toList}
        // Route: ${routingTable.v.ids}
        // Neigh: ${neighbourhood.unique}
        // ========================================"""
    }
}

