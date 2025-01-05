package vp

import stainless.lang.*
import stainless.annotation.*
import stainless.collection.*
import StainlessProperies.*
import NetworkHelpers.*
import scala.annotation.threadUnsafe

case class PastryNetwork(nodes: List[PastryNode],l: BigInt){
    require(l>0
        && (l/2 + l/2) == l
        && nodes.size >= l
        && all_nodes_valid(nodes) // all the nodes must be valid
        && isSortedByNodeId(nodes)
        && eachNodeAccountableOwnData(nodes))

    // def isValidHelper(l: List[PastryNode]): Unit = {
    //     require(l.forall(n=>n.isValid))
    //     l match{
    //         case Nil() => 
    //         case Cons(h, t) => {
    //             assert(h.isValid)
    //             assert(h.own_data.isValid)
    //             isValidHelper(t)
    //         } 
    //     }
    // }.ensuring(l.forall(n=>n.own_data.isValid))

    // def iuwrtIsCallable(l: List[PastryNode]) : Unit = {
    //     require(l.forall(n=>n.isValid))
    //     isValidHelper(l)
    // }.ensuring(isUniqueWRT(l,n=>n.own_data) || !isUniqueWRT(l,n=>n.own_data))

    // def is_synched(): Boolean = {
    //     true //nodes.forall(node => node.is_ready())
    // }

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

    def drop(nodes_to_drop: List[PastryNode]): PastryNetwork = {
        //require(isValid)
        require(isSortedByNodeId(nodes_to_drop))
        require(all_nodes_valid(nodes_to_drop))
        require(all_nodes_in_network(nodes_to_drop))
        // Because we don't have a circular list, we want to ensure that 
        //all the nodes we are dropping are not "on the border", otherwise we wouldn't have replacement nodes to select from the leafset
        require(allNotLimitNodes(nodes_to_drop)) 
        // require(nodes.forall(node => {
        //     assert(node.isValid)
        //     node.leafset.intersectSize(get_ids(nodes_to_drop)) < l/2
        // }))
        this
        // TODO Implement drop
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
            case stainless.collection.Cons(x,xs) => {vp.Cons(x.id,get_ids(xs))}
        }
    }.ensuring(ret => ret.isValid && ret.size() == node_list.size)
}

// --------------------- Proofs -----------------------------------

@ghost
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


    // def dropIsCorrectEasy(n: PastryNetwork, dropped_nodes: List[PastryNode]): Unit ={
    //     require(n.is_synched()) 
    //     require(dropped_nodes.forall(node => n.nodes.contains(node)))
    //     require(dropped_nodes.size < n.l/2 ) // This is a stricter condition than the one we really need which woule be:
    //     // require(n.nodes.forall(node=> (node.leafset & Set(dropped_nodes)).size() > (n.l/2) ))
    //     decreases(dropped_nodes)

    // }.ensuring(_ => n.drop(dropped_nodes).containsAll(n.all_keys().toList))
}