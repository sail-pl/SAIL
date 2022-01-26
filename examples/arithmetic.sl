process Main(){
    var x : int;
    var z : int;
    x = 1 + 2;
    {
        var y : int;
        y = x + 3 * 2;
        z = y;
    }
    print_int(x);
    print_string(" ");
    print_int(z);
    print_newline();
}