process Main(){

    var x : box<int>;
    {
        var y : box<int> = box(1);
        x = y
    }
    // Error
     //print_int(*x); print_newline();
    // print_int(y); print_newline()
    x = box(3)
}