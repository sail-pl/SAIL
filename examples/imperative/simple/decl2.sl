import test_utils

process Main {
Run:
    {
        var x : int = 0
    }
    // Error 
    // print_int(x); print_newline();
    while (1 < 0){
        var x : int = 1
    }
    // print_int(x); print_newline();
    exit(0);
}
