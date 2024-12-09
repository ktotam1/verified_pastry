// package vp

// import stainless.lang.*
// import stainless.annotation.*
// import stainless.collection.*



// @ghost
// object ExtraListProps{
//     def p0[T](sl: stainless.collection.List[T],l:BigInt): Unit={
//         require(sl.size == l)
//         require(sl.unique.size==l)
//         require(l>=0)
        
//         (sl,sl.unique) match{
//             case (stainless.collection.Nil(), stainless.collection.Cons(x,xs)) => assert(false)
//             case (stainless.collection.Cons(x,xs), stainless.collection.Nil()) => assert(false)
//             case (stainless.collection.Cons(x,xs), stainless.collection.Cons(y,ys)) => {
//                 assert(x==y)
//                 p0(xs,l-1)
//             }
//         }

//     }.ensuring(sl==sl.unique)

//     def p1[T](sl: stainless.collection.List[T],l:BigInt,e: T): Unit ={
//         // This property states that if {a stainless list of size L, containing only unique elements (i.e. its `.unique` is also of size l),
//         // which contains an element e} then {removing that element from the list will yield a list of size L-1}
//         require(sl.size == l)
//         require(sl.unique.size == l)
//         require(sl.contains(e))
//         require(l>=0)

//         // def inner_rec(rest: stainless.collection.List[T]): Unit{
//         //     rest match{
//         //         case 
//         //         case Cons(x,xs) =>
//         //     }
//         // }

//     }.ensuring((sl.unique - e).size == (l-1))
// }