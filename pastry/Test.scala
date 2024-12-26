package pastry 
import stainless.collection.*
import stainless.io.StdOut.println
import stainless.lang.*
import utils.* 

object Test{
    def main(args: Array[String]) = {
        val network = Network( Cell(MutableNil()))
        val rf = 2
        val node0 = Node(1, rf, network)
        network.add(node0)
        // val ids = List(2,3)
        // val ids = List(2,1000000000,1000000001,2000000000,2000000001)
        val ids = List(10,11,123456789, 123456799, Int.MaxValue-2,Int.MaxValue-1)
        ids.forall(i => {
            val node = Node(i,rf, network)
            network.add(node)
            node.forward(Join(node.id, List[Int]()), node.id, node0.id)
            true
        })
        // network.nodes.v.forall(x => {
        //         // println(x.mkSting())
        //         true
        //     })
        node0.send(Msg("hi!", node0.id), 123456800)
        // val node = Node(0,rf)
        // node.forward(Join(node.id, List[Int]()), node.id, node0.id)

    }
}