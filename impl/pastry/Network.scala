package pastry 
// import stainless.collection.*
import stainless.lang.*
import utils.*

class Network(val nodes: Cell[MutableList[Node]]) { 
   
    def add(node: Node): Unit = {
        node.init()
        nodes.v = nodes.v :+ node
    }

    def send(msg: Message, key: Int, to: Int): Unit = {
        decreases(dist(key,to))
        def foreach(nodes: MutableList[Node]): Unit = {
            decreases(nodes.length)
            nodes match 
                case MutableNil() => 
                case MutableCons(x,xs) => 
                    if x.id == to then
                        x.receive(msg, key) 
                    else 
                        foreach(xs)
        }
        foreach(nodes.v)
    }
}