import test_utils

method f(x : int) : int{
    return x;
}
process Main {
Init:
Loop:

    print_int(f(1));
    exit(0);
}
