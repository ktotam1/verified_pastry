package pastryMath

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

def leftSmaller(x: Int, y: Int, id: Int): Boolean = {
    dist(y,id) < dist(x,id)
}

def rightSmaller(x: Int, y: Int, id: Int): Boolean = { 
    dist(x,id) < dist(y,id)
}

//ring less than 
def rlt(x: Int,y: Int): Boolean = {
    if abs(x-y) < abs(max(x,y)-Int.MaxValue - min(x,y)) then 
        x < y
    else 
        x > y
}   

def shl(a: Int, b: Int): Int = {
        var i = 0
        var done = false 
        while(i <= 32 && !done) {
            if (a >> i == b >> i) 
                done = true 
            else 
                i += 1
        }
        32-i
}