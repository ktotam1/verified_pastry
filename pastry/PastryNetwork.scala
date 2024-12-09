package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*


sealed trait NodeState{
    def is_ready(): Boolean
}

object NodeState{
    case object Synched extends NodeState{
        override def is_ready(): Boolean = true 
    }
    case object Dead extends NodeState{
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
case class PastryNode(id: Int, l: BigInt, state: NodeState, routingTable: SortedList,leafset: SortedList, own_data: List[Int], leafset_data: Set[Int]){
    require((l/2 + l/2) == l) // assume L divisible by 2
    require(leafset.size() == l) // the leafset is of size L (it is constructed such that the first L/2 elements are nodes ids of the L/2 left-closest nodes to ourselve, and the next L/2 elements -- of the right-closest)
    require(leafset.isValid)
    require(!own_data.exists(key=>leafset_data.contains(key))) // our data must not be in the leafset_data 
    require(routingTable.isValid) // the routing table must be sorted by closest elements (defined as closest node id for this part of the exercise)
    
    //require(leafset.forall(node => routingTable.contains(node)))


    def is_ready(): Boolean = state.is_ready()

    def remove_from_ls_and_replace(dropped_node: PastryNode,replacing_node:PastryNode,take_ownership:Boolean): PastryNode = {
        require(leafset.contains(dropped_node.id))
        require(!leafset.contains(replacing_node.id))
        require(dropped_node.id != id) // can't drop yourself
        require(dropped_node.state == vp.NodeState.Dead)
        require(replacing_node.state == vp.NodeState.Synched)
        val new_ls = leafset.remove(dropped_node.id)
        assert(new_ls.size() == l-1)
        val nnls = new_ls.insert(replacing_node.id)
        assert(nnls.size() == l)
        assert(nnls.isValid)
        val newrt = routingTable.merge(replacing_node.routingTable)
        assert(newrt.isValid)
        val new_data = if !take_ownership then own_data else own_data ++ dropped_node.own_data
        val new_leafset_data = if !take_ownership then leafset_data ++ replacing_node.leafset_data else leafset_data ++ replacing_node.leafset_data -- dropped_node.own_data.toSet

        PastryNode(id,l,state,newrt,new_ls,new_data,new_leafset_data)
    }// .ensuring((ret:PastryNode) => dropped_node.own_data.forall(k=>ret.own_data.contains(k)) && own_data.forall(k=>ret.own_data.contains(k)))
}

case class PastryNetwork(nodes: List[PastryNode],l: BigInt){
    require(isvalidstainless(nodes,node=>node.id))

    def node_ids(): SortedList = {
        fromStainlessSortedList(nodes,node=>node.id)
    }.ensuring((res:SortedList)=>res.isValid)
    // We ignore "too small" networks, which don't even have l nodes
    require(nodes.size >= l)

    def is_synched(): Boolean = {
        nodes.forall(node => node.is_ready())
    }

    def size() : BigInt = nodes.size
    
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
        require(isvalidstainless(nodes_to_drop,node=>node.id))
        require(!nodes_to_drop.exists(dropped_node => node_ids().isFirstLastK(l/2,dropped_node.id)))
        this
        // TODO Implement drop
    }
    //def join(node: PastryNode): PastryNetwork
}

// --------------------- Proofs -----------------------------------

@ghost
object PastryProps{
    import PastryNetwork.*

    


    // def dropIsCorrectEasy(n: PastryNetwork, dropped_nodes: List[PastryNode]): Unit ={
    //     require(n.is_synched()) 
    //     require(dropped_nodes.forall(node => n.nodes.contains(node)))
    //     require(dropped_nodes.size < n.l/2 ) // This is a stricter condition than the one we really need which woule be:
    //     // require(n.nodes.forall(node=> (node.leafset & Set(dropped_nodes)).size() > (n.l/2) ))
    //     decreases(dropped_nodes)

    // }.ensuring(_ => n.drop(dropped_nodes).containsAll(n.all_keys().toList))
}