import pastry.*
import pastryMath.leftSmaller
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
        for (i <- 1 to 10)
            val node = Node(Math.pow(10,i).toInt,rf)
            network.add(node)
            node.send(Join(node.id), node.id, node0.id)
        network.nodes.forall(x => {
                println(x.mkSting())
                true
            })
        println("Done")
    }
}