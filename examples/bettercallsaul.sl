method sum(x : int , y : int) : int{
    return x + y;
}

method f(x : &int) {
    *x = 27;
    return;
}

process Main(){
    sum (5, 7);
    var x : int = sum (8,7);
    var y : int;
    var z : int;
    y = & x;
    f(y);
    f(&z);
    signal s;
    print_newline();
}