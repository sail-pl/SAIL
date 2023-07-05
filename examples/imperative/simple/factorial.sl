import test_utils

method factorial(x : int) : int {
    if (x==0 or x==1 ) return 1
    else return x * factorial(x - 1)
}

process Main {
Init:
Loop:

    var x : int;
    x = factorial (5);
    print_int(x); 
    print_newline();
    exit(0);
}
