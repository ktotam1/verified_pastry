import sorted.*
object Test{
    def main(args: Array[String]) = {
        var s: SortedList = Nil
        s.insert(-2147483648)
        print(s.remove(-2147483648))
    }
}