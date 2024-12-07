import scala.collection.immutable.HashMap
class Node[K,V](key: Int, replicationFactor: Int) {

    val values = HashMap[K,V]()
    val routingTable = HashMap[Int, Node[K,V]]() 
    val leafset = Array.ofDim[Node[K,V]](replicationFactor)

    def joinRequest(other: Node[K,V]): Boolean = {
        false
    }

    def get(key: K): Option[V] = {
        None
    }

    def set(key: K, value: V): Unit = {

    }
}