import print_utils
enum option<A>{
    None,
    Some(A)
}

struct list<A>{
   head : option<box<node<A>>> 
}

struct node<A>{
    elem : A,
    next : option<box<node<A>>>
}

method length<A>(l : list<A>) : int {
    var pt : option<box<node>> = l.head;
    var cpt : int = 0;
    while (pt != None){
        case (pt) {
           None : {},
           Some (e) : pt = (*e).next; cpt = cpt+1
        };
    }
    return cpt
}

method fromTo(n : int, m : int) : list<int> {
    var node : option<box<node<A>>> = None;
    var current : int = m;
    while (current >= n) {
        node = Some(box(node{elem : n, next:node}));
        current = current - 1
    }
    return list {head : node}    
}

process Main(){
    var x : node<int> = node {elem:1, next:None};
    var y : node<int> = node {elem:2, next:Some(box(x))};
    var t : node<int> = node {elem:3, next:Some(box(y))};
    var z : list<int> = list {head:Some(box(t))};
    var n : int = length(z);
    print_int(n); print_newline();
    var l : list<int> = fromTo(0,10);
    var u : int = length(l);
    print_int(u);print_newline();
    print_int(length(l));print_newline()
}