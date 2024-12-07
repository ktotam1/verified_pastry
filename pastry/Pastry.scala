import scala.collection.immutable.HashMap

trait Purpose
case class Get(key: Int)
case class Reply(value: String)
case class Set(key: Int, value: String)
case class Gossip() // idk what this does yet, maybe exchanges routing tables or something 

case class Message(to: Int, from: Int, purpose: Purpose)



class Node(key: Int, replicationFactor: Int) {
    val values = HashMap[Int,String]()
    val routingTable = HashMap[Int, Node]() //id to Node to send things to
    val leafset = Array.ofDim[Node](replicationFactor)

    var network: Network = Network() 

    def get(key: Int): Option[String] = {
        None
    }

    def set(key: Int, value: String): Unit = {

    }

    def receive(msg: Message): Unit = { 
        msg.purpose match {
            case Get(x) => print(x)
        }
    }
}

class Network { 
    var nodes: List[Node] = List()
    def add(node: Node) = {
        node.network = this //potential aliasing problem ? 
        nodes = node +: nodes
    }

    def send(msg: Message) = {
        msg.purpose match {
            case Get(x) => print(x)
        }
    }
}