struct s {
    x : int
}

struct t {
    x : box<s>
}

process Main(){

    var x : box<int> = box(42);
    *x = 18;
    *x  = *x + 1;
    print_int(*x);

    var y : s = s {x : 3};
    print_int(y.x);
    y.x = 2;
    print_int(y.x);
    print_int(1);

    //var z : array<int> = [1,2,3];
    //z[0]=5;
    //print_int(z[0]);

    var a : t = t { x: box(1)};
    *(a.x) = 18;
    print_int(*(a.x))
}