import test_utils
struct point {
    x : int,
    y : int,
    z : box<int>
}

process Main () {
    
    var a : point = point{x : 0, y: 0,z:box(1)};
    var u : int = 1;
 //   a.x = a.y;
 //   var b : &Point = &a;
 //   var c : Point = *b;
//    var d : int = * (a.z);
    quit();
}