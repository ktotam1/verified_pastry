import pastry.*
object Test{
    def main(args: Array[String]) = {
        val network = Network()
        val rf = 2
        val node0 = Node(1, rf)
        network.add(node0)
        for (i <- 1 to 6)
            val node = Node(Math.pow(10,i).toInt,rf)
            network.add(node)
            node0.send(Join(node.id), node.id, node0.id)
        network.nodes.forall(x => {
                println(x.mkSting())
                true
            })
        println("Done")
    }
}