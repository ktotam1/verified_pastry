package pastry 
import stainless.collection.*
import stainless.lang.* 

sealed trait Message
case class Join(newId: Int, path: List[Int]) extends Message //request to join. as this message gets passed along people add their own ids
case class JoinReply(newId: Int, path: List[Int]) extends Message //give the joiner the people he needs to contact 
case class JoinNotice(myId: Int) extends Message //when you joined and you need to inform people
case class Empty() extends Message
case class Msg(text: String, from: Int) extends Message //for debugging purposes
case class AskForState(requesterId: Int) extends Message
case class RoutingTableState(rtID: Int, routingTableMap: Map[Int, List[Int]]) extends Message
case class LeafSetState(leafSet: List[Int], from: Int) extends Message
// case class Error(reason: String) extends Message
