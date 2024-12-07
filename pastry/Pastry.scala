import scala.collection.immutable.HashMap

trait Purpose
case class Get(key: Int) extends Purpose
case class Reply(value: String) extends Purpose
case class NotFound() extends Purpose
case class Set(key: Int, value: String) extends Purpose
case class Gossip() extends Purpose // idk what this does yet, maybe exchanges routing tables or something 
case class Empty() extends Purpose 
case class Error(reason: String) extends Purpose

case class Message(to: Int, from: Int, purpose: Purpose)

case class Node(id: Int, replicationFactor: Int) {
    val values = HashMap[Int,String]()
    val routingTable = HashMap[Int, Node]() 
    val leafset = Array.ofDim[Node](replicationFactor)

    var network: Network = Network() 

    def getNextHop(key: Int): Int = {
        0
    }

    def get(key: Int): Option[String] = {
        None
    }

    def set(key: Int, value: String): Unit = {
        val nextHop = getNextHop(key)
        network.send()
    }

    def send(msg: Message): Purpose = { 
        msg.purpose match {
            case Get(x) => Empty()
        }
    }
}

class Network { 
    var nodes: List[Node] = List()
    def add(node: Node) = {
        node.network = this //potential aliasing problem ? 
        nodes = node +: nodes
    }

    def send(msg: Message): Purpose = {
        var x: Purpose = Error(s"Node with id ${msg.to} not found")
        nodes.foreach(n => if (n.id == msg.to) { x = n.send(msg)})
        x
    }
}