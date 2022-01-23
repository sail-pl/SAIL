method min(x : int, y : int, z : int) : int {
    if (x < y) 
        if (y < z) return x;
        else if (x < z) return x; else return z;
    else 
        if (x < z) return y;
        else if (y < z) return y; else return z;
}

process Main(){

    var x : int;
    x = min(5,3,6);
    print_int(x);
    print_newline();
}