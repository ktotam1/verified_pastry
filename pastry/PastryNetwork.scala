package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import StainlessConverter.*
import stainless.annotation.cCode.drop


// sealed trait NodeState{
//     def is_ready(): Boolean
// }

// object NodeState{
//     case object Synched extends NodeState{
//         override def is_ready(): Boolean = true 
//     }
//     case object Dead extends NodeState{
//         override def is_ready(): Boolean = false 
//     }
// }



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
case class PastryNode(id: Int, l: BigInt, routingTable: SortedList,leafset: SortedList, own_data: List[Int], leafset_data: Set[Int]){
    /*
        For some reason, stainless isn't really good at using Properties proven outside of a class 

        Therefeore, instead of having class invariants, such as 
        
        ```
        require((l/2 + l/2) == l) // assume L divisible by 2
        require(leafset.size() == l) // the leafset is of size L (it is constructed such that the first L/2 elements are nodes ids of the L/2 left-closest nodes to ourselve, and the next L/2 elements -- of the right-closest)
        require(leafset.isValid)
        require(!own_data.exists(key=>leafset_data.contains(key))) // our data must not be in the leafset_data 
        require(routingTable.isValid) // the routing table must be sorted by closest elements (defined as closest node id for this part of the exercise)
        ```

        which would've been a very elegant way to model this, I will rewrite this using an `isValid` function, and only properties
    */
    def isValid: Boolean = {
        (l/2 + l/2) == l &&
        leafset.size() == l && 
        leafset.isValid &&
        routingTable.isValid
    }

       
    // ?? require(leafset.forall(node => routingTable.contains(node))) 


    //def is_ready(): Boolean = state.is_ready() : Ignore state for now, it adds nothing


    def remove_from_ls_and_replace(dropped_node: PastryNode,replacing_node:PastryNode,take_ownership:Boolean): PastryNode = {
        require(isValid)
        require(dropped_node.isValid)
        require(replacing_node.isValid)
        require(leafset.contains(dropped_node.id))
        require(!leafset.contains(replacing_node.id))
        require(dropped_node.id != id) // can't drop yourself
        
        val new_ls = leafset.remove(dropped_node.id).insert(replacing_node.id)
        val newrt = routingTable.merge(replacing_node.routingTable)
        
        val new_data = if !take_ownership then own_data else own_data ++ dropped_node.own_data
        val new_leafset_data = if !take_ownership then leafset_data ++ replacing_node.leafset_data else leafset_data ++ replacing_node.leafset_data -- dropped_node.own_data.toSet

        PastryNode(id,l,newrt,new_ls,new_data,new_leafset_data)
    }//.ensuring((ret:PastryNode) => dropped_node.own_data.forall(k=>ret.own_data.contains(k)) && own_data.forall(k=>ret.own_data.contains(k)))
      // Might have to rewrite a minimal example of  that poscondition to check whether it can actually be proven with List[Int]
      // Otherwise can adapt own_data to become a SortedList as well! Could help with the class invariant too
}

case class PastryNetwork(nodes: List[PastryNode],l: BigInt){
    require(isvalidstainless(nodes,node=>node.id))
    // We ignore "too small" networks, which don't even have l nodes
    require(nodes.size >= l)

    def node_ids(): SortedList = {
        fromStainlessSortedList(nodes,node=>node.id)
    }.ensuring((res:SortedList)=>res.isValid)

    def is_synched(): Boolean = {
        true //nodes.forall(node => node.is_ready())
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
    import slProperties.*

    def nodeBuiltFromRemoveHasCorrectLS(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode) : Unit ={
        require(start.isValid)
        require(dropped_node.isValid)
        require(replacement.isValid)
        require(start.leafset.contains(dropped_node.id))
        require(!start.leafset.contains(replacement.id))
        require(dropped_node.id != start.id) // can't drop yourself
        removeElementYouContainDecreasesSize(start.leafset,dropped_node.id,start.l)
        ncImplremoveNc(start.leafset,replacement.id,dropped_node.id)
        insertNewElementIncreasesSize(start.leafset.remove(dropped_node.id),replacement.id,start.l-1)
    }.ensuring(start.leafset.remove(dropped_node.id).insert(replacement.id).size() == (start.l))

    def nodeBuiltFromRemoveIsValid(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode,to: Boolean): Unit = {
        require(start.isValid)
        require(replacement.isValid)
        require(dropped_node.isValid)
        require(start.leafset.contains(dropped_node.id))
        require(!start.leafset.contains(replacement.id))
        require(dropped_node.id != start.id) // can't drop yourself
        
        nodeBuiltFromRemoveHasCorrectLS(start,dropped_node,replacement)
        val built = start.remove_from_ls_and_replace(dropped_node,replacement,to)

        assert(built.leafset.size() == start.l) // Stainless, istg, just use nodeBuiltFromRemoveHasCorrectLS arghhhhhhhhhh
        assert(built.leafset.isValid)
        assert(built.routingTable.isValid)
    }.ensuring(start.remove_from_ls_and_replace(dropped_node,replacement,to).isValid)

    // def dropIsCorrectEasy(n: PastryNetwork, dropped_nodes: List[PastryNode]): Unit ={
    //     require(n.is_synched()) 
    //     require(dropped_nodes.forall(node => n.nodes.contains(node)))
    //     require(dropped_nodes.size < n.l/2 ) // This is a stricter condition than the one we really need which woule be:
    //     // require(n.nodes.forall(node=> (node.leafset & Set(dropped_nodes)).size() > (n.l/2) ))
    //     decreases(dropped_nodes)

    // }.ensuring(_ => n.drop(dropped_nodes).containsAll(n.all_keys().toList))
}