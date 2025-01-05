package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import StainlessProperies.*

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
case class PastryNode(id: Int, l: BigInt, routingTable: SortedList,leafset: SortedList, own_data: SortedList, leafset_data: SortedList){
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
        routingTable.isValid &&
        own_data.isValid &&
        leafset_data.isValid &&
        own_data.removeAll(leafset_data) == own_data
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
        require(own_data.removeAll(replacing_node.own_data) == own_data) // our data doesn't contain the replacing node's data
        
        val new_ls = leafset.remove(dropped_node.id).insert(replacing_node.id)
        val newrt = routingTable.merge(replacing_node.routingTable)
        
        val new_data = if !take_ownership then own_data else own_data.merge(dropped_node.own_data)
        val new_leafset_data = if !take_ownership then leafset_data.merge(replacing_node.own_data) else leafset_data.merge(replacing_node.own_data).removeAll(dropped_node.own_data)

        PastryNode(id,l,newrt,new_ls,new_data,new_leafset_data)
    }//.ensuring((ret:PastryNode) => dropped_node.own_data.forall(k=>ret.own_data.contains(k)) && own_data.forall(k=>ret.own_data.contains(k)))
      // Might have to rewrite a minimal example of  that poscondition to check whether it can actually be proven with List[Int]
      // Otherwise can adapt own_data to become a SortedList as well! Could help with the class invariant too
}


@ghost
object PastryNodeProps{
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

    def nodeBuiltFromRemovePreservesStartData(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode,to: Boolean): Unit={
        require(start.isValid)
        require(dropped_node.isValid)
        require(replacement.isValid)
        require(start.leafset.contains(dropped_node.id))
        require(!start.leafset.contains(replacement.id))
        require(dropped_node.id != start.id) // can't drop yourself
        require(start.own_data.removeAll(replacement.own_data) == start.own_data) // our data doesn't contain the replacing node's data
        
        val built = start.remove_from_ls_and_replace(dropped_node,replacement,to)
        if !to then{
            assert(built.own_data == start.own_data)
            subsetReflexivity(start.own_data)
        }
        else{
            assert(built.own_data == start.own_data.merge(dropped_node.own_data))
            alwaysSubsetOfMerged(start.own_data,dropped_node.own_data)
        }
    }.ensuring(start.own_data.isSubsetOf(start.remove_from_ls_and_replace(dropped_node,replacement,to).own_data))

    def nodeBuiltFromRemovePreservesDroppedDataWhenTO(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode): Unit = {
        require(start.isValid)
        require(dropped_node.isValid)
        require(replacement.isValid)
        require(start.leafset.contains(dropped_node.id))
        require(!start.leafset.contains(replacement.id))
        require(dropped_node.id != start.id) // can't drop yourself
        require(start.own_data.removeAll(replacement.own_data) == start.own_data) // our data doesn't contain the replacing node's data
        
        val built = start.remove_from_ls_and_replace(dropped_node,replacement,true)
        assert(built.own_data == start.own_data.merge(dropped_node.own_data))
        mergeCommutativity(start.own_data,dropped_node.own_data)
        alwaysSubsetOfMerged(dropped_node.own_data,start.own_data)
    }.ensuring(dropped_node.own_data.isSubsetOf(start.remove_from_ls_and_replace(dropped_node,replacement,true).own_data))

    def buildDataNotInLeafsetData(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode,to: Boolean): Unit = {
        require(start.isValid)
        require(dropped_node.isValid)
        require(replacement.isValid)
        require(start.leafset.contains(dropped_node.id))
        require(!start.leafset.contains(replacement.id))
        require(dropped_node.id != start.id) // can't drop yourself
        require(start.own_data.removeAll(replacement.own_data) == start.own_data) // our data doesn't contain the replacing node's data
        val built = start.remove_from_ls_and_replace(dropped_node,replacement,to)
        assert(start.own_data.removeAll(start.leafset_data) == start.own_data) // From isValid
        if !to then{
            assert(built.own_data == start.own_data)
            assert(built.leafset_data == start.leafset_data.merge(replacement.own_data))
            assert(start.own_data.removeAll(replacement.own_data) == start.own_data) // from require
            removeAllMergeISRemoveAllRemoveAll(start.own_data,start.leafset_data,replacement.own_data)
            assert(start.own_data.removeAll(start.leafset_data.merge(replacement.own_data)) == start.own_data) // Must reach this
            assert(built.own_data.removeAll(built.leafset_data) == built.own_data) // Must reach this
        }
        else{
            assert(built.own_data == start.own_data.merge(dropped_node.own_data))
            assert(built.leafset_data == start.leafset_data.merge(replacement.own_data).removeAll(dropped_node.own_data))
            assert(start.own_data.removeAll(replacement.own_data) == start.own_data)// from require
            
            alwaysSubsetOfMerged(dropped_node.own_data,start.own_data)
            removeAllRemoveAllSubIsRemoveAllMerge(start.own_data.merge(dropped_node.own_data),start.leafset_data.merge(replacement.own_data),dropped_node.own_data)
            assert(start.own_data.merge(dropped_node.own_data)
                    .removeAll(start.leafset_data.merge(replacement.own_data).removeAll(dropped_node.own_data)) 
                    == start.own_data.merge(dropped_node.own_data)
                    .removeAll(start.leafset_data.merge(replacement.own_data))
                    .merge(dropped_node.own_data))

            mergeRemoveAllisRemoveAllMerge(start.own_data,dropped_node.own_data,start.leafset_data.merge(replacement.own_data))
            mergeDistributivityOne(start.own_data.removeAll(start.leafset_data.merge(replacement.own_data)),dropped_node.own_data.removeAll(start.leafset_data.merge(replacement.own_data)),dropped_node.own_data)
            
            
            subsetReflexivity(dropped_node.own_data)
            removeAllRemoveAllSubIsRemoveAllMerge(dropped_node.own_data,start.leafset_data.merge(replacement.own_data),dropped_node.own_data)
            removeAllImpliesSubset(dropped_node.own_data,start.leafset_data.merge(replacement.own_data))
            subsetMergeSupersetEqSuperset(dropped_node.own_data.removeAll(start.leafset_data.merge(replacement.own_data)),dropped_node.own_data)

            assert(start.own_data.removeAll(start.leafset_data) == start.own_data) // From isValid, see above
            assert(start.own_data.removeAll(replacement.own_data) == start.own_data)// from require, see above
            removeAllMergeISRemoveAllRemoveAll(start.own_data,start.leafset_data,replacement.own_data)

            assert(start.own_data.merge(dropped_node.own_data)
            .removeAll(start.leafset_data.merge(replacement.own_data).removeAll(dropped_node.own_data))
             == start.own_data.merge(dropped_node.own_data)) // Must reach this

            assert(built.own_data.removeAll(built.leafset_data) == built.own_data) // Must reach this
        }
    }.ensuring(start.remove_from_ls_and_replace(dropped_node,replacement,to).own_data.removeAll(start.remove_from_ls_and_replace(dropped_node,replacement,to).leafset_data) == start.remove_from_ls_and_replace(dropped_node,replacement,to).own_data)

    def nodeBuiltFromRemoveIsValid(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode,to: Boolean): Unit = {
        require(start.isValid)
        require(dropped_node.isValid)
        require(replacement.isValid)
        require(start.leafset.contains(dropped_node.id))
        require(!start.leafset.contains(replacement.id))
        require(dropped_node.id != start.id) // can't drop yourself
        require(start.own_data.removeAll(replacement.own_data) == start.own_data) // our data doesn't contain the replacing node's data
        
        
        nodeBuiltFromRemoveHasCorrectLS(start,dropped_node,replacement)

        val built = start.remove_from_ls_and_replace(dropped_node,replacement,to)

        assert(built.leafset.size() == start.l)
        assert(built.leafset.isValid)
        assert(built.routingTable.isValid)
        //startDataisSubsetOfnbfrData(start,dropped_node,replacement,to)
        //assert(start.own_data.isSubsetOf(built.own_data))
        buildDataNotInLeafsetData(start,dropped_node,replacement,to)        
    }.ensuring(
        start.remove_from_ls_and_replace(dropped_node,replacement,to).isValid
        
    )   

}