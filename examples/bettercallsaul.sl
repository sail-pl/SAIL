method sum(x : int , y : int) : int{
    return x + y;
}

method f(x : &int) {
    *x = sum (8,7);
    return;
}

process Main(){
    var x : int;
    var y : int;
    var z : int;
    y = & x;
    f(y);
    f(&z);
    print_int(x);
    print_string(" ");
    print_int(*y);
    print_string(" ");
    print_int(z);
    print_newline();
}