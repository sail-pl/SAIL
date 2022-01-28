process Main(){
    var cpt : int = 0;

    var x : box<int>;
    while (cpt < 1)
    {
        var y : box<int> = box(1);
        x = y;
        cpt = cpt + 1
    }
    // Error x is points to the box which has been freed
    // print_int(*x); print_newline();
    x = box(5) // needed otherwise we will try to drop the box a second time
}