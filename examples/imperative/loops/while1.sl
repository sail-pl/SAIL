import test_utils

process Main {
Run:
    var mut x : int = 0;
    while (x < 10){
        print_string("Hello\n");
        x = x + 1
    }
    print_int(x);
    print_string(" Worlds\n");
    exit(0);
}
