import test_utils
enum color {
    Red,
    Black
}

struct point {x:int, y:int, c:color}

process Main {
Init:
Loop:

    var p : point = point {x:5, y:7, c:Red};
    var y : int = p.x + p.y;
    var z : color = p.c;
    exit(0);
}