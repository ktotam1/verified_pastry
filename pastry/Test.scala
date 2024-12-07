object Test{
    def main(args: Array[String]) = {
        val network: Network = Network()
        val nodes: List[Node] = (for i <- 0 to 5 yield Node(i, 2)).toList
        nodes.foreach(x => network.add(x))
    }
}