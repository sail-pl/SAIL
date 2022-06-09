struct point {
    x : int,
    y : int
}

struct pointBis {
    z : point
}

process Main() {
    
    var a : point = point {x:0,y:0};
    var b : &point = &a;
    (*b).x = 1;
    (*b).y = 1;
    print_int((*b).y);
    var c : pointBis = pointBis{z:b};
    (*c.z).x = 2;
    print_int(a.x);
}