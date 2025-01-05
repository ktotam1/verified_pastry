# CS550 - Formal Verification 
## Verified Pastry
In this project, we aim to formally verify aspects of the Pastry DHT and PAST distributed archive storage system. In `impl/` you will find a Pastry implementation in Scala, while in `verif/` there is verification code for a more basic PAST system, as well as many verified helper data types.  

To run the verification `cd` in `verif/` and run `stainless PastryNetwork.scala PastryNode.Scala SortedList.scala` !

