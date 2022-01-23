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
        case (l) {
           None : {};
           Some (e) : {pt = e.next; cpt = cpt+1;} 
        }
    }
    return cpt;
}

process Main(){
    var x : node<int> = {elem:1, next:None};
    var y : node<int> = {elem:2, next:Some(box(x))};
    var z : list<int> = {head:Some(box(y))};
    print_int(y.elem); print_newline();
    //print_int(length(z));
}