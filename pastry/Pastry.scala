import scala.collection.immutable.HashMap
import stainless.collection.*

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

    var network: Network = Network(0) 

    // shared prefix
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

    def getNextHop(key: Int): Int = {
        0
    }

    def get(key: Int): Option[String] = {
        if values.contains(key) then
            values.get(key)
        else 
            val nextHop = getNextHop(key)
            network.send(Message(nextHop, id, Get(key))) match
                case Reply(value) => Option(value)
                case _ => None
    }

    def set(key: Int, value: String): Unit = {
        val nextHop = getNextHop(key)
        network.send(Message(nextHop, id, Set(key, value)))
    }

    def send(msg: Message): Purpose = { 
        msg.purpose match {
            case Get(key) => {
                get(key) match 
                    case None => Empty()
                    case Some(value) => Reply(value)
            }
            case Set(key, value) => {
                set(key, value)
                Empty()
            }
            case _ => Empty()
        }
    }
}

class Network(maxNodes: Int) { 
    var nodes: Array[Node] = Array.ofDim[Node](maxNodes)
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