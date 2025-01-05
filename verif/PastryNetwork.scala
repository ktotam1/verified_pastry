package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import StainlessProperies.*
import NetworkHelpers.*
case class PastryNetwork(nodes: List[PastryNode],l: BigInt){
    import ListNodesProperiesNotNeededIfSortedListGeneric.*
    import PastryNetworkProps.*
    import PastryNodeProps.*
    require(l>2 // the l/2-1 bound doesn't work for l=2
        && (l/2 + l/2) == l
        && nodes.size > l
        && all_nodes_valid(nodes) // all the nodes must be valid
        && isSortedByNodeId(nodes)
        && eachNodeAccountableOwnData(nodes))


    def size() : BigInt = nodes.size

    def all_keys(): SortedList = {
        //require(isValid)
        def innerAKFL(acc:SortedList,rest:List[PastryNode]): SortedList = {
            require(acc.isValid)
            require(all_nodes_valid(rest))
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

    def all_nodes_in_network(l:List[PastryNode]): Boolean ={
        // All the nodes we are dropping are nodes in the network        
        //require(isValid)
        l match{
            case stainless.collection.Nil() => true
            case stainless.collection.Cons(x,xs) => {
                nodes.contains(x) && all_nodes_in_network(xs)
            }
        }
    }

    def isAmongstLimitNodes(node:PastryNode,threshold:BigInt): Boolean = {
        require(threshold>=0 && threshold <= nodes.size)
        get_ids(nodes).isFirstLastK(threshold,node.id)
    }

    // def notisAmongstImplNotFirst(node:PastryNode,threshold:BigInt): Unit` = {
    //     require(threshold>=0)
    //     require(!isAmongstLimitNodes(node,threshold))
    // }.ensuring()

    def allNotLimitNodes(nodes_to_drop: List[PastryNode]): Boolean = {
        //require(isValid)
        require(isSortedByNodeId(nodes_to_drop))
        assert(l>=2)
        
        nodes_to_drop match{
            case stainless.collection.Nil() => true
            case stainless.collection.Cons(x,xs) => {
                !isAmongstLimitNodes(x,l/2-1) && allNotLimitNodes(xs)
            }
        }
        // In the properties, we prove that this ensures:
        // get_ids(network.nodes).take(network.l/2-1).removeAll(get_ids(nodes_to_drop)) == get_ids(network.nodes).take(network.l/2-1) && 
        // get_ids(network.nodes).takeLast(network.l/2-1).removeAll(get_ids(nodes_to_drop)) == get_ids(network.nodes).takeLast(network.l/2-1)
        // aka the nodes removed are not part of the limit
    }

    def underDropBound(nodes_to_drop: List[PastryNode]): Boolean = {
        require(all_nodes_valid(nodes_to_drop))
        require(isSortedByNodeId(nodes_to_drop))
        val drop_node_ids = get_ids(nodes_to_drop)
        nodes match{
            case stainless.collection.Nil() => true
            case stainless.collection.Cons(x,xs) => {
                x.leafset.intersectSize(drop_node_ids) <= l/2 - 1 // <=> < l/2
            }
        }
    }

    def dropRecOnPotentiallyRemovedNodes(leftSafe: List[PastryNode],vulnNodes: List[PastryNode],rightSafe: List[PastryNode],nodes_to_drop: List[PastryNode]): PastryNetwork={
        //Drop requirements
        require(isSortedByNodeId(nodes_to_drop))
        require(all_nodes_valid(nodes_to_drop))
        require(all_nodes_in_network(nodes_to_drop))
        require(allNotLimitNodes(nodes_to_drop)) 
        require(underDropBound(nodes_to_drop))

        // forall ids, left < vuln < right 
        require(nodes == (leftSafe ++ vulnNodes ++ rightSafe))
        require(isSortedByNodeId(leftSafe)) // Automatically implied from mergePreservesMultipleSort, but there is no clean way to do this in stainless
        require(isSortedByNodeId(vulnNodes))
        require(isSortedByNodeId(rightSafe))

        //  left - vuln = left <=> left inter vuln = 0
        require(get_ids(leftSafe).removeAll(get_ids(vulnNodes)) == get_ids(leftSafe))
        // vuln - right = vuln <=> vuln inter right = 0
        require(get_ids(vulnNodes).removeAll(get_ids(rightSafe)) == get_ids(vulnNodes))
        // left - right = left <=> left inter right = 0
        require(get_ids(leftSafe).removeAll(get_ids(rightSafe)) == get_ids(leftSafe))
        // left and right are "safe", aka don't belong in the nodes that will be dropped
        require(get_ids(leftSafe).removeAll(get_ids(nodes_to_drop)) == get_ids(leftSafe))
        require(get_ids(rightSafe).removeAll(get_ids(nodes_to_drop)) == get_ids(rightSafe))

        require(leftSafe.size + rightSafe.size >= l-2)
        decreases(vulnNodes.size+nodes_to_drop.size)

        mergePreservesMultipleSort(nodes,leftSafe,vulnNodes,rightSafe)
        orderedImpliesOrdered(nodes,leftSafe,vulnNodes,rightSafe)
        (nodes_to_drop,vulnNodes) match{
            case (stainless.collection.Nil(),_)=>{
                // we drop no nodes, great
                this
            }
            case (Cons(d,ds),stainless.collection.Nil())=>{
                // we have no vulnerable nodes, great :)
                this
            }
            case (Cons(d,ds),Cons(m,ms)) =>{
                mergeAddOnePreservesMerge(leftSafe,vulnNodes,leftSafe++vulnNodes)
                get_idsTransparentToRemAllSupSubAndremAllPreserveIntersectDef(leftSafe,vulnNodes)
                isSortedByIdImplTailIsSortedById(vulnNodes)
                isSortedByNodeIdImplAppendBiggerHeadPreservesSort(leftSafe,vulnNodes,leftSafe ++ vulnNodes)
                get_idsTransparentToalwaysSubsetOfMerged(vulnNodes,rightSafe)
                get_idsTransparentToSupersetInv(leftSafe,rightSafe,m)
                get_idsTransparentToSupersetInv(leftSafe,nodes_to_drop,m)
                get_idsTransparentWhenPrependSmaller(rightSafe,nodes_to_drop,m)
                // Some nodes are dropped, too bad :(
                if (d.id != m.id) then {
                    // But not this vulnerable one!
                    dropRecOnPotentiallyRemovedNodes(leftSafe :+ m,ms,rightSafe,nodes_to_drop)
                }
                else{
                    // But this one!
                    (leftSafe,rightSafe) match{
                        case (stainless.collection.Nil(),stainless.collection.Nil()) => {
                            assert(leftSafe.size == 0)
                            assert(rightSafe.size == 0)
                            assert(leftSafe.size + rightSafe.size < l-2)
                            assert(false) // this case is impossible :)
                        }
                        case (stainless.collection.Cons(x,xs),stainless.collection.Nil()) =>{
                            // Same case as the more complex Cons below, copy pasted the proof, except now we take the leftmost node as replacement:
                            val closestNode = x
                            val replacementNode = xs.head
                            val updatedNode = closestNode.remove_from_ls_and_replace(m,replacementNode,true)
                            nodeBuiltFromRemoveIsValid(closestNode,m,replacementNode,true) 
                            nodeBuiltFromRemovePreservesDroppedDataWhenTO(closestNode,m,replacementNode)
                            nodeBuiltFromRemovePreservesStartData(closestNode,m,replacementNode,true)
                            buildDataNotInLeafsetData(closestNode,m,replacementNode,true) 
                            val newNetwork = PastryNetwork((leftSafe:+updatedNode)++vulnNodes++rightSafe,l)
                            assert(newNetwork.all_keys() == all_keys())
                            newNetwork.dropRecOnPotentiallyRemovedNodes(leftSafe:+updatedNode,ms,rightSafe,ds)
                        }
                        case (stainless.collection.Nil(),stainless.collection.Cons(y,ys)) =>{
                            // Symmetrical to above
                            val closestNode = y
                            val replacementNode = ys.last
                            val updatedNode = closestNode.remove_from_ls_and_replace(m,replacementNode,true)
                            nodeBuiltFromRemoveIsValid(closestNode,m,replacementNode,true) 
                            nodeBuiltFromRemovePreservesDroppedDataWhenTO(closestNode,m,replacementNode)
                            nodeBuiltFromRemovePreservesStartData(closestNode,m,replacementNode,true)
                            buildDataNotInLeafsetData(closestNode,m,replacementNode,true) 
                            val newNetwork = PastryNetwork((leftSafe:+updatedNode)++vulnNodes++rightSafe,l)
                            assert(newNetwork.all_keys() == all_keys())
                            newNetwork.dropRecOnPotentiallyRemovedNodes(leftSafe:+updatedNode,ms,ys,ds)
                        }
                        case (stainless.collection.Cons(x,xs),stainless.collection.Cons(y,ys)) =>{
                            val closestNode = x // arbitrarily selected between both
                            val replacementNode = ys.last
                            val updatedNode = closestNode.remove_from_ls_and_replace(m,replacementNode,true)
                            // We get a valid Node:
                            nodeBuiltFromRemoveIsValid(closestNode,m,replacementNode,true) 
                            // The data of our dropped node is a subset of the data of our updateNode
                            nodeBuiltFromRemovePreservesDroppedDataWhenTO(closestNode,m,replacementNode)
                            // And the closestNode's data is kept as well
                            nodeBuiltFromRemovePreservesStartData(closestNode,m,replacementNode,true)
                            // Furthermore, the built node doesn't contain data from the leafset data, this would have been helpful for the leafset invariant
                            buildDataNotInLeafsetData(closestNode,m,replacementNode,true) 
                            
                            // Now we just need to update the network.
                            // Since the replacement node was a safe node, we can just put it back in the list, and continue iterating over all other nodes to drop
                            val newNetwork = PastryNetwork((leftSafe:+updatedNode)++vulnNodes++rightSafe,l)
                            assert(newNetwork.all_keys() == all_keys())
                            newNetwork.dropRecOnPotentiallyRemovedNodes(leftSafe:+updatedNode,ms,rightSafe,ds)
                        }
                    }
                }
            }
                
        }
    }.ensuring((dropped:PastryNetwork) => all_keys() == dropped.all_keys())

    def drop(nodes_to_drop: List[PastryNode]): PastryNetwork = {
        //require(isValid)
        require(isSortedByNodeId(nodes_to_drop))
        require(all_nodes_valid(nodes_to_drop))
        require(all_nodes_in_network(nodes_to_drop))
        // Because we don't have a circular list, we want to ensure that 
        //all the nodes we are dropping are not "on the border", otherwise we wouldn't have replacement nodes to select from the leafset
        require(allNotLimitNodes(nodes_to_drop)) 
        require(underDropBound(nodes_to_drop))
        
        // left and right are safe
        allNotLimitNodesEnsuresRemoveAllPreservation(this,nodes_to_drop)
        assert(get_ids(nodes).take(l/2-1).removeAll(get_ids(nodes_to_drop)) == get_ids(nodes).take(l/2-1)) 
        assert(get_ids(nodes).takeLast(l/2-1).removeAll(get_ids(nodes_to_drop)) == get_ids(nodes).takeLast(l/2-1))
        get_idsTransparentToTake(nodes,l/2-1)
        get_idsTransparentToTakeLast(nodes,l/2-1)
        //We build the new network by recursion on all the current 
        //network's nodes (past the safety bound), rather than by recursion on the 
        
        val first_safe_nodes = nodes.take(l/2-1)
        takePreservesIdOrdering(nodes,l/2-1)
        val potentially_removed_nodes = nodes.slice(l/2-1,size()-(l/2-1))
        slicePreservesIdOrdering(nodes,l/2-1,size()-(l/2-1))
        get_idsTransparentToSlice(nodes,l/2-1,size()-(l/2-1))
        val last_safe_nodes = nodes.slice(size()-(l/2-1),size())
        slicePreservesIdOrdering(nodes,size()-(l/2-1),size())
        get_idsTransparentToremSubsetPreservation(potentially_removed_nodes,last_safe_nodes,nodes_to_drop)
        get_idsTransparentToremSubsetPreservation(first_safe_nodes,potentially_removed_nodes,nodes_to_drop)
        get_idsTransparentToremSubsetPreservation(first_safe_nodes,last_safe_nodes,nodes_to_drop)

        sliceSliceUnion(nodes,l/2-1,size()-(l/2-1))

        dropRecOnPotentiallyRemovedNodes(first_safe_nodes,potentially_removed_nodes,last_safe_nodes,nodes_to_drop)

    }.ensuring((dropped:PastryNetwork) => all_keys() == dropped.all_keys())
    //def join(node: PastryNode): PastryNetwork
}

object NetworkHelpers{
    def all_nodes_validIMPLall_ownDataValid(l: List[PastryNode]): Unit = {
        require(all_nodes_valid(l))
        l match{
            case stainless.collection.Nil[PastryNode]() => {}
            case stainless.collection.Cons(x,xs) => {
                assert(x.isValid)
                assert(x.own_data.isValid)
                all_nodes_validIMPLall_ownDataValid(xs)
            }
        }
    }.ensuring(all_lists_valid(l.map(n=>n.own_data)))

    def eachNodeAccountableOwnData(l: List[PastryNode]): Boolean = {
        // each node is accountable for its own data, each datum is accounted for by only one node (other nodes only have potential replicas only, tho this isn't verified here)
        require(all_nodes_valid(l))
        all_nodes_validIMPLall_ownDataValid(l)
        allIntersectionEmpty(l.map(n=>n.own_data))
    }

    def all_nodes_valid(l: List[PastryNode]): Boolean = {
       l match{
            case stainless.collection.Nil[PastryNode]() => true
            case stainless.collection.Cons(x,xs) => {x.isValid && all_nodes_valid(xs)}
        }
    }

    def isSortedByNodeId(l:List[PastryNode]): Boolean = {
        // the nodes must be stored by their ids
        // equivalent to isvalidstainless(nodes,node=>node.id), but we eventually
        // decided to not use it because of the predicate name substitution issue 
        l match {
            case stainless.collection.Nil[PastryNode]() => true
            case stainless.collection.Cons(x,stainless.collection.Nil[PastryNode]()) => {
                true
            }
            case stainless.collection.Cons(x,xs) =>{
                (x.id < xs.head.id) && isSortedByNodeId(xs)
            }
        }
    }

    def get_ids(node_list:List[PastryNode]): SortedList={        
        require(isSortedByNodeId(node_list))
        node_list match{
            case stainless.collection.Nil() => vp.Nil
            case stainless.collection.Cons(x,xs) => {
                val res = vp.Cons(x.id,get_ids(xs))
                assert(res.head == x.id)
                res
            }
        }
    }.ensuring(ret => ret.isValid && ret.size() == node_list.size)
}

object ListNodesProperiesNotNeededIfSortedListGeneric{
    // See report:
    // The methods here are marked @library because we have already proven 
    // them for SortedList, but did not manage to make SortedList generic
    // (i.e., currently you can interpret SortedList as SortedList[Int], we have
    // just not managed to make a stainless-compilable generic version SortedList[T : Ordering : Validator])  (we have a scala compilable version)
    
    @library
    def takePreservesIdOrdering(l:List[PastryNode],k:BigInt): Unit = {
        require(isSortedByNodeId(l))
        // If we had a custom ordering in a generic SortedList, we wouldn't have needed this because:
        //  Order preservation --> l.take().isSorted
        //  But l.take().isValid
        //  and l.isValid == l.isSorted and l.isUnique
        // QED
        //We therefore mark this as @library
    }.ensuring(isSortedByNodeId(l.take(k)))
    // @library
    // def dropPreservesIdOrdering(l:List[PastryNode],k:BigInt): Unit = {
    //     require(isSortedByNodeId(l))
    //     // same argument as take
    // }.ensuring(isSortedByNodeId(l.drop(k)))
    @library
    def slicePreservesIdOrdering(l:List[PastryNode],from:BigInt, to:BigInt): Unit = {
        require(isSortedByNodeId(l))
        // same argument as take
    }.ensuring(isSortedByNodeId(l.slice(from,to)))

    // The following methods simply follow from the fact that get_ids conceptually corresponds to
    // l.map(node=>node.id)
    // We would not have needed to have these methods had we had a generic sorted list
    // (even without the map, the match iteration would have sufficed as the "complicated" part would have been to 
    // require that the ids are sorted, which we already do!)
    // It is therefore evident that get_ids is transparent 
    @library
    def get_idsTransparentToTake(l: List[PastryNode],k:BigInt): Unit = {
        require(isSortedByNodeId(l))
        require(0<=k && k<= l.size)
    }.ensuring(get_ids(l.take(k)) == get_ids(l).take(k))
    @library
    def get_idsTransparentToTakeLast(l: List[PastryNode],k:BigInt): Unit = {
        require(isSortedByNodeId(l))
        require(0<=k && k<= l.size)
    }.ensuring(get_ids(l.slice(l.size-k,l.size)) == get_ids(l).takeLast(k))
    @library 
    def get_idsTransparentToSlice(l: List[PastryNode],from:BigInt,to:BigInt): Unit = {
        require(isSortedByNodeId(l))
        require(from >= 0 && from <= l.size)
        require(to >= 0 && to <= l.size)
        require(from<to)
    }.ensuring(get_ids(l.slice(from,to)) == get_ids(l).slice(from,to))

    @library
    def get_idsTransparentToremSubsetPreservation(l:List[PastryNode],subset:List[PastryNode],superset:List[PastryNode]):Unit ={
        require(isSortedByNodeId(l))
        require(isSortedByNodeId(subset))
        require(isSortedByNodeId(superset))
        // We couldn't require the subset property because of a weird stainless error, namely:
            //ADT Object must appear only in strictly positive positions of Object
        // otherwise, we need: 
            //l.content - superset.content == l
            //subset.content.subsetOf(superset.content)
        // but this yields the aforementionned error

        // by takeRemoveDropIsTake for left.removeAll(right) == left
        // and by remAllSupersetSubsetPreservesEquality, which we didn't have time to finish proving
    }.ensuring(get_ids(l).removeAll(get_ids(subset)) == get_ids(l))
    @library
    def get_idsTransparentToRemAllSupSubAndremAllPreserveIntersectDef(a:List[PastryNode],b:List[PastryNode]): Unit = {
        require(isSortedByNodeId(a))
        require(isSortedByNodeId(b))
        require(get_ids(a).removeAll(get_ids(b)) == get_ids(a))
        require(b!=stainless.collection.Nil())
        // alwaysSubsetOfMerged remAllpreservesEmptyIntersectdef and remAllSupersetSubsetPreservesEquality and 
    }.ensuring(get_ids(a :+ b.head).removeAll(get_ids(b.tail)) == get_ids(a :+ b.head))
    @library
    def get_idsTransparentToalwaysSubsetOfMerged(a:List[PastryNode],b:List[PastryNode]): Unit = {
        require(isSortedByNodeId(a))
        require(isSortedByNodeId(b))
        require(get_ids(a).removeAll(get_ids(b)) == get_ids(a))
        require(a!=stainless.collection.Nil())
        // alwaysSubsetOfMerged remAllpreservesEmptyIntersectdef 
    }.ensuring(get_ids(a.tail).removeAll(get_ids(b)) == get_ids(a.tail))
    @library
    def get_idsTransparentToSupersetInv(a:List[PastryNode],b:List[PastryNode],x:PastryNode): Unit = {
        require(isSortedByNodeId(a))
        require(isSortedByNodeId(b))
        require(get_ids(a).removeAll(get_ids(b)) == get_ids(a))
        // alwaysSubsetOfMerged remAllSupersetSubsetPreservesEquality
    }.ensuring(get_ids(a:+x).removeAll(get_ids(b)) == get_ids(a:+x))
    


    @library
    def isSortedByNodeIdImplAppendBiggerHeadPreservesSort(l:List[PastryNode],q:List[PastryNode],evidence:List[PastryNode]):Unit={
        require(isSortedByNodeId(evidence))
        require((l++q) == evidence)
        require(q!=stainless.collection.Nil())
        //Append in a sorted List corresponds to insert, which preserves the sort
        // evidence here corresponds to simply saying that l < q
        // Conceptually uses mergePreservesMultipleSort to ensure that both l and q are sorted
    }.ensuring(isSortedByNodeId(l :+ q.head))

    @library
    def mergePreservesMultipleSort(evidence:List[PastryNode],l1:List[PastryNode],l2:List[PastryNode],l3:List[PastryNode]): Unit={
        require(evidence == (l1 ++ l2 ++ l3))
        require(isSortedByNodeId(evidence))
        // The first line directly comes from merge preserving sort order.
        // The second line comes from mergeDistributivity/Associativity
    }.ensuring(
        isSortedByNodeId(l1) && isSortedByNodeId(l2) && isSortedByNodeId(l3)
        && isSortedByNodeId(l1++l2) && isSortedByNodeId(l1++l3) && isSortedByNodeId(l2++l3)
    )

    @library
    def isSortedByIdImplTailIsSortedById(l:List[PastryNode]):Unit={
        require(isSortedByNodeId(l))
        require(l!=stainless.collection.Nil())
        //Automatically comes from tail.isValid
    }.ensuring(isSortedByNodeId(l.tail))

    @library
    def mergeAddOnePreservesMerge(l: List[PastryNode],q: List[PastryNode],evidence: List[PastryNode]) : Unit = {
        require((l ++ q) == evidence)
        require(q!=stainless.collection.Nil())
    }.ensuring(((l:+q.head) ++ (q.tail)) == evidence)

    @library
    def orderedImpliesOrdered(evidence:List[PastryNode],l1:List[PastryNode],l2:List[PastryNode],l3:List[PastryNode]): Unit={
        require(evidence == (l1 ++ l2 ++ l3))
        require(isSortedByNodeId(evidence))
        //This was not proven, as we couldn't establish properties on sorted lists of lists, since we didn't have generic lists in the first place to start with
    }.ensuring(l1.head.id < l2.head.id && l2.head.id < l3.head.id)
}

object InvariantsNeeded{
    //The following object holds some invariants over our network we didn't have time to prove,
    // yet we need to ensure drop validity (our PastryNode.remove_from_ls_and_replace correctly assumes they hold)
    // To be able to have a provable final project, we will therefore just assume they always hold
    @library
    def uniqueInvariant(a:PastryNode,b:PastryNode): Unit = {
        //require(a.id!=b.id && c.id!=a.id && b.id!=c.id)
        require(a.id!=b.id)
        //three different nodes have the 
    }.ensuring(a.own_data.removeAll(b.own_data) == a.own_data)
}

// --------------------- Proofs -----------------------------------
object PastryNetworkProps{
    import slProperties.*

    def isAmongstLimitNodesImplFirstOrLastContains(network:PastryNetwork,node:PastryNode,threshold:BigInt): Unit = {
        require(threshold>=0 && threshold <= network.nodes.size)
        require(network.isAmongstLimitNodes(node,threshold))
    }.ensuring(get_ids(network.nodes).take(threshold).contains(node.id) || get_ids(network.nodes).takeLast(threshold).contains(node.id))

    def nisAmongstLimitNodesImplFirstOrLastContains(network:PastryNetwork,node:PastryNode,threshold:BigInt): Unit = {
        require(threshold>=0 && threshold <= network.nodes.size)
        require(!network.isAmongstLimitNodes(node,threshold))
    }.ensuring(!get_ids(network.nodes).take(threshold).contains(node.id) && !get_ids(network.nodes).takeLast(threshold).contains(node.id))


    def allNotLimitNodesEnsuresRemoveAllPreservation(network:PastryNetwork,nodes_to_drop: List[PastryNode]): Unit = {
        //require(isValid)
        require(isSortedByNodeId(nodes_to_drop))
        require(network.allNotLimitNodes(nodes_to_drop))
        val ids_1 = get_ids(network.nodes).take(network.l/2-1)
        val ids_2 = get_ids(network.nodes).takeLast(network.l/2-1)
        val removed_ids = get_ids(nodes_to_drop)
        val removed_1 = ids_1.removeAll(removed_ids)
        val removed_2 = ids_2.removeAll(removed_ids)
        if ids_1 == vp.Nil then removeAllNilIsNil(removed_ids)
        if ids_2 == vp.Nil then removeAllNilIsNil(removed_ids)
        else{
            nodes_to_drop match{
                case Nil() =>{
                    assert(removed_1 == ids_1)
                    assert(removed_2 == ids_2)
                }
                case Cons(x,xs) =>{
                    assert(!network.isAmongstLimitNodes(x,network.l/2-1))
                    nisAmongstLimitNodesImplFirstOrLastContains(network,x,network.l/2-1)
                    removeAllNotContainsHeadEqRemoveAllTail(ids_1,removed_ids)
                    removeAllNotContainsHeadEqRemoveAllTail(ids_2,removed_ids)
                    allNotLimitNodesEnsuresRemoveAllPreservation(network,xs)
                }
            }
        }
    }.ensuring(
        get_ids(network.nodes).take(network.l/2-1).removeAll(get_ids(nodes_to_drop)) == get_ids(network.nodes).take(network.l/2-1) && 
        get_ids(network.nodes).takeLast(network.l/2-1).removeAll(get_ids(nodes_to_drop)) == get_ids(network.nodes).takeLast(network.l/2-1)
    )


    // Hereunder, methods we have not had time to prove :(
    @library
    def sliceSliceUnion[T](l:List[T],from:BigInt,to:BigInt): Unit = {
        require(from >= 0 && from <= l.size)
        require(to >= 0 && to <= l.size)
        require(from<to)
        // Equivalent of SortedList sliceSliceUnion
    }.ensuring((l.take(from) ++ l.slice(from,to) ++ l.slice(to,l.size) )== l)

    @library
    def get_idsTransparentWhenPrependSmaller(a:List[PastryNode],b:List[PastryNode],x:PastryNode): Unit = {
        require(isSortedByNodeId(a))
        require(isSortedByNodeId(b))
        require(get_ids(a).removeAll(get_ids(b)) == get_ids(a))
        require(x.id<a.head.id)
    }.ensuring(get_ids(x::a).removeAll(get_ids(b)) == get_ids(x::a))
}