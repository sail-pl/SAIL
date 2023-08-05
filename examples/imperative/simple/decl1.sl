import test_utils

process Main {
    Run:
    var x : int;
    x = 3;
    print_int(x);
    print_newline();
    exit(0);
}
