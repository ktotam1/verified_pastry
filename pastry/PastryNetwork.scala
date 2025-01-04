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

case class PastryNetwork(nodes: List[PastryNode],l: BigInt){
    def isValidHelper(l: List[PastryNode]): Unit = {
        require(l.forall(n=>n.isValid))
        l match{
            case Nil() => 
            case Cons(h, t) => {
                assert(h.isValid)
                assert(h.own_data.isValid)
                isValidHelper(t)
            } 
        }
    }.ensuring(l.forall(n=>n.own_data.isValid))

    def iuwrtIsCallable(l: List[PastryNode]) : Unit = {
        require(l.forall(n=>n.isValid))
        isValidHelper(l)
    }.ensuring(isUniqueWRT(l,n=>n.own_data) || !isUniqueWRT(l,n=>n.own_data))

    
    def isValid: Boolean = {
        isvalidstainless(nodes,node=>node.id) // the nodes must be stored in an ordered set fashion
        // We ignore "too small" networks, which don't even have l nodes
        && nodes.size >= l
        && nodes.forall(node=>node.isValid) // all the nodes must be valid
        && 
        {
            iuwrtIsCallable(nodes)
            isUniqueWRT(nodes,node=>node.own_data) // each node is accountable for its own data, each datum is accounted for by only one node (other nodes only have replicas)
        }
    }

    def node_ids(): SortedList = {
        require(isValid)
        fromStainlessSortedList(nodes,node=>node.id)
    }.ensuring((res:SortedList)=>res.isValid)

    def is_synched(): Boolean = {
        true //nodes.forall(node => node.is_ready())
    }

    def size() : BigInt = nodes.size
    
    def is_empty(): Boolean = {
        size() == 0
    }

    def all_keys(): SortedList = {
        require(isValid)
        def innerAKFL(acc:SortedList,rest:List[PastryNode]): SortedList = {
            require(acc.isValid)
            require(rest.forall(n=>n.isValid))
            rest match{
                case Nil() => acc
                case Cons(x, xs) => {
                    assert(x.isValid)
                    innerAKFL(acc.merge(x.own_data),xs)
                }
            }
        }.ensuring((ret:SortedList) => ret.isValid)
        innerAKFL(vp.Nil,nodes)
    }.ensuring(_.isValid)

    def contains(element: Int): Boolean = {
        nodes.exists(node => node.own_data.contains(element))
    }
    def containsAll(elements: List[Int]): Boolean = {
        elements.forall(e => contains(e))
    }

    def get_ids(node_list:List[PastryNode]): SortedList={        
        require(isvalidstainless(node_list,node=>node.id))
        node_list match{
            case stainless.collection.Nil() => vp.Nil
            case stainless.collection.Cons(x,xs) => {vp.Cons(x.id,get_ids(xs))}
        }
    }

    def drop(nodes_to_drop: List[PastryNode]): PastryNetwork = {
        require(isValid)
        require(nodes_to_drop.forall(node => nodes.contains(node))) // All the nodes we are dropping are nodes in the network        
        require(isvalidstainless(nodes_to_drop,node=>node.id))
        require(!nodes_to_drop.exists(dropped_node => node_ids().isFirstLastK(l/2,dropped_node.id)))
        require(nodes.forall(node => node.leafset.subsetSize(get_ids(nodes_to_drop)) < l/2))
        this
        // TODO Implement drop
    }.ensuring((dropped:PastryNetwork) => dropped.isValid && all_keys() == dropped.all_keys())
    //def join(node: PastryNode): PastryNetwork
}

// --------------------- Proofs -----------------------------------

@ghost
object PastryProps{
    import slProperties.*

    // def innerFl(node:PastryNode,acc:SortedList): Unit = {
    //     require(node.isValid)
    //     require(acc.isValid)
    // }.ensuring(acc.merge(node.own_data).isValid)

    // def stainlessFlPreserversValidity(start: List[PastryNode],acc: SortedList): Unit = {
    //     require(start.forall(node=>node.isValid))
    //     require(acc.isValid)
    //     start match {
    //         case Nil() =>
    //         case Cons(node, xs) => {
    //             assert(acc.isValid)
    //             assert(node.own_data.isValid)
    //             innerFl(node,acc)
    //             assert(acc.merge(node.own_data).isValid)
    //             stainlessFlPreserversValidity(xs,acc.merge(node.own_data))
    //         }
    //     }
    // }.ensuring(start.foldLeft(acc)((a,n) => a.merge(n.own_data)).isValid)

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

    def startDataisSubsetOfnbfrData(start:PastryNode,dropped_node:PastryNode,replacement:PastryNode,to: Boolean): Unit={
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
        startDataisSubsetOfnbfrData(start,dropped_node,replacement,to)
        assert(start.own_data.isSubsetOf(built.own_data))

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
            
            removeAllRemoveAllIsRemoveAllMerge(start.own_data.merge(dropped_node.own_data),start.leafset_data.merge(replacement.own_data),dropped_node.own_data)
            assert(start.own_data.merge(dropped_node.own_data)
                    .removeAll(start.leafset_data.merge(replacement.own_data).removeAll(dropped_node.own_data)) 
                    == start.own_data.merge(dropped_node.own_data)
                    .removeAll(start.leafset_data.merge(replacement.own_data))
                    .merge(dropped_node.own_data))

            mergeRemoveAllisRemoveAllMerge(start.own_data,dropped_node.own_data,start.leafset_data.merge(replacement.own_data))
            
            
            removeAllRemoveAllIsRemoveAllMerge(dropped_node.own_data,start.leafset_data.merge(replacement.own_data),dropped_node.own_data)
            mergeDistributivityOne(start.own_data.removeAll(start.leafset_data.merge(replacement.own_data)),dropped_node.own_data.removeAll(start.leafset_data.merge(replacement.own_data)),dropped_node.own_data)
            subsetReflexivity(dropped_node.own_data)
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
    }.ensuring(start.remove_from_ls_and_replace(dropped_node,replacement,to).isValid)

    // def dropIsCorrectEasy(n: PastryNetwork, dropped_nodes: List[PastryNode]): Unit ={
    //     require(n.is_synched()) 
    //     require(dropped_nodes.forall(node => n.nodes.contains(node)))
    //     require(dropped_nodes.size < n.l/2 ) // This is a stricter condition than the one we really need which woule be:
    //     // require(n.nodes.forall(node=> (node.leafset & Set(dropped_nodes)).size() > (n.l/2) ))
    //     decreases(dropped_nodes)

    // }.ensuring(_ => n.drop(dropped_nodes).containsAll(n.all_keys().toList))
}