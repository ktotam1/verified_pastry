//> using jar "stainless-library-sources.jar"
//> using jar "stainless-library.jar"
//> using scala "3.5.0"

package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*

import vp.SortedList
//import utils.OrderedListMap.*


sealed trait NodeState{
    def is_ready(): Boolean
}

object NodeState{
    case object Synched extends NodeState{
        override def is_ready(): Boolean = true 
    }
    case object RouteUpdate extends NodeState{
        override def is_ready(): Boolean = false 
    }
    case object DataLSUpdate extends NodeState{
        override def is_ready(): Boolean = false 
    }
}



/**
    A node in a Pastry Network
    @param id the (unique) id of that node
    @param l the maximum network-defined leafset size
    @param state the state of the node
    @param routingTable a sorted list of node (identified by their id)
    @param leafset a set of nodes 
    @param data the set of data keys this particular node holds that are "its own". 
                Note that this could've been a Map (e.g.: Samuel Chassot's (Ordered)ListMap) if we wanted to prove some "robustness"/"synchronization" properties about the system.
                However, since we are interested only in the system's partition-tolerance capabilities, we ignore the values and only keep track of the keys 
    @param leafset_data the set of data keys that our node keeps track of for replication purposes on behalf of the nodes in its leafset
*/
case class PastryNode(id: Int, l: Int, state: NodeState, routingTable: SortedList,leafset: List[Int], own_data: List[Int], leafset_data: Set[Int]){
    require(leafset.size == l)
    require(leafset.forall(node => routingTable.contains(node)))

    def is_ready(): Boolean = state.is_ready()

    def remove_from_ls(dropped_node: PastryNode): PastryNode = {
        require(leafset.contains(dropped_node.id))
        require
        val new_ls = leafset - dropped_node.id
        
    }
}

case class PastryNetwork(nodes: List[PastryNode],l: Int){
    // We ignore "too small" networks, which don't even have l nodes
    require((nodes.size >= l) && (nodes.size < Int.MaxValue))

    def is_synched(): Boolean = {
        nodes.forall(node => node.is_ready())
    }

    def size() : Int = nodes.size.intValue()
    
    def is_empty(): Boolean = {
        size() == 0
    }

    def all_keys(): Set[Int] = {
        nodes.foldLeft(Set())((set,node) => set++node.own_data.toSet)
    }
    def contains(element: Int): Boolean = {
        nodes.exists(node => node.own_data.contains(element))
    }
    def containsAll(elements: List[Int]): Boolean = {
        elements.forall(e => contains(e))
    }


    def drop(nodes_to_drop: List[PastryNode]): PastryNetwork = {
        require(is_synched()) // the network must be in steady state
        require(nodes_to_drop.forall(node => nodes.contains(node))) // All the nodes we are dropping are nodes in the network        
        decreases(nodes_to_drop)

        // TODO Implement drop
    }
    //def join(node: PastryNode): PastryNetwork
}

// --------------------- Proofs -----------------------------------

@ghost
object PastryProps{
    import PastryNetwork.*

    def dropIsCorrectEasy(n: PastryNetwork, dropped_nodes: List[PastryNode]): Unit ={
        require(n.is_synched()) 
        require(dropped_nodes.forall(node => n.nodes.contains(node)))
        require(dropped_nodes.size < n.l/2 ) // This is a stricter condition than the one we really need which woule be:
        // require(n.nodes.forall(node=> (node.leafset & Set(dropped_nodes)).size() > (n.l/2) ))
        decreases(dropped_nodes)

    }.ensuring(_ => n.drop(dropped_nodes).containsAll(n.all_keys().toList))
}