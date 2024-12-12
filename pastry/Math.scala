package pastry
import stainless.lang.BigInt
def abs(x: Int): Int = {
    if x < 0 then -x else x
}
def min(x: Int, y: Int): Int = {
    if x > y then y else x
}
def max(x: Int, y: Int): Int = {
    if x > y then x else y
}
def dist(x:Int, y:Int): Int = {
    min(abs(x-y), abs(max(x,y)-Int.MaxValue - min(x,y)))
}

def stepsLeft(x: Int, y: Int): Int = {
    if x == y then 0
    else if x > y then 
        x - y
    else 
        Int.MaxValue - y + x
}

def leftSmaller(x:Int,y:Int, wrt: Int): Boolean = {
    stepsLeft(wrt,x) > stepsLeft(wrt,y)
}

def stepsRight(x: Int, y: Int): Int = {
    if x == y then 0
    else if x < y then 
        y - x
    else 
        Int.MaxValue - x + y
}

def rightSmaller(x: Int, y: Int, wrt: Int): Boolean = {
    stepsRight(wrt,x) < stepsRight(wrt,y)

}

//ring less than 
def rlt(x: Int,y: Int): Boolean = {
    if abs(x-y) < abs(max(x,y)-Int.MaxValue - min(x,y)) then 
        x < y
    else 
        x > y
}   

def shl(a: Int, b: Int): Int = {
    var i: Int = 1
    var j = 0
    var done = false
    while(!done){
        if j==10 || a/i == b/i then
            done = true
        else 
            i *= 10
            j += 1
    }
    10-j
        // var i = 0
        // var done = false 
        // while(i <= 32 && !done) {
        //     if (a >> i == b >> i) 
        //         done = true 
        //     else 
        //         i += 1
        // }
        // 32-i
}