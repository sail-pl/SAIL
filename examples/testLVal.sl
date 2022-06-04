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

process Main(){

    var x : list<box<int>>;
    var n0 : node = node { elem : box(1), next : None };
    var n1 : node = node { elem : box(3), next : None };
    var n2 : node = node { elem : box(5), next : None };
    n1.next = Some (n2);
    n0.next = Some (n1);
    x = list { head : Some (n0)};
    var a : array<box<int>> = [box(0),box(0)];
    case (x.head) {
        Some (m) : {
            *a[*box(0)] = *m.elem;
            case (m.next) {
                Some (n) : {
                    *n.elem = *n.elem + 1;
                    *a[*box(1)] = *n.elem;
                    n.next = None
                },
                None : {}
        }},
        None : {}
    };
    var y : int = *a[0] + *a[1];
    if (y == 5) print_string ("OK\n") else print_string ("KO\n")
}