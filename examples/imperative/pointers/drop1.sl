import test_utils
process Main {
Init:
Loop:


    var x : box<int>;
    {
        var y : box<int> = box(1);
        x = y
        // print_int(*y); print_newline() ==> Error, y was moved
    }
    // Error
     //print_int(*x); print_newline();
    // print_int(y); print_newline()
    x = box(3);
    exit(0);
}