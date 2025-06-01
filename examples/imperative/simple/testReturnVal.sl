import test_utils

method f(x : int) : int{
    return x;
}
process Main {
Run:
    print_int(f(1));
    quit();
}
