object Test{
    def shl(a: Int, b: Int): Int = {
        var i = 0
        var done = false 
        while(i <= 32 && !done) {
            println(s"i $i a ${a>>i} b ${b>>i}")
            if (a >> i == b >> i) 
                done = true 
            else 
                i += 1
        }
        32-i
    }

    def main(args: Array[String]) = {
        val a = 0b00
        val b = 0b11
        val c = 0b1110
        val d = 0b1101
        println(a)
        println(b)
        println(shl(a,b))
        println(shl(c,d))
    }
}