package pastry 
import stainless.collection.*

trait Message
case class Join(newId: Int) extends Message
case class JoinNotice(newId: Int) extends Message
case class Empty() extends Message
case class Msg(text: String) extends Message //for debugging purposes
case class requestState(requesterId: Int) extends Message
case class RoutingTableState(routingTable: RoutingTable) extends Message
case class LeafSetState(leafSet: List[Int], from: Int) extends Message
case class Error(reason: String) extends Message
