import pastry.*
import pastryMath.leftSmaller
import stainless.collection.*

object Test{
    def main(args: Array[String]) = {
        // val s = LeafSet(10000, true)
        // for (i <- 0 to 6)
        //     s.insert(Math.pow(10, i).toInt)
        // println(s.toList)
        // println(s.id)
        // println(s.isSorted())
        val network = Network()
        val rf = 2
        val node0 = Node(1, rf)
        network.add(node0)
        // val ids = List(2,3)
        val ids = List(2,1000000000,1000000001,2000000000,2000000001)
        ids.forall(i => {
            val node = Node(i,rf)
            network.add(node)
            node.forward(Join(node.id, List[Int]()), node.id, node0.id)
            true
        })
        network.nodes.forall(x => {
                println(x.mkSting())
                true
            })
        node0.send(Msg("hi!", node0.id), 1000000001)
        // val node = Node(0,rf)
        // node.forward(Join(node.id, List[Int]()), node.id, node0.id)

    }
}