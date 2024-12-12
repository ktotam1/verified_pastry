package pastry 
import stainless.collection.*
import stainless.lang.*
class Network(var nodes: List[Node] = List()) { 
    def add(node: Node) = {
        node.network = this //potential aliasing problem ? 
        nodes = node :: nodes
    }

    def send(msg: Message, key: Int, to: Int): Option[Error] = {
        def foreach(nodes: List[Node]): Option[Error] = {
            nodes match 
                case stainless.collection.Nil() => Option(Error("Node not found"))
                case x :: xs => 
                    if x.id == to then
                        x.receive(msg, key) 
                        None()
                    else 
                        foreach(xs)
        }
        foreach(nodes)
    }
}