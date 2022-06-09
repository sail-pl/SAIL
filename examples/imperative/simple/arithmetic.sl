process Main(){
    var x : int = 0;
    var z : int;
    {
        var y : int;
        y = x + 3 * 2;
        z = y
    }
    print_int(z);
    print_newline()
}