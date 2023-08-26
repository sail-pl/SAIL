import test_utils
method g<T>(a : T) : T {
    return a;
}

method f<T>(a : T) : T {
    return g(a);
}

process Main {
Init:
Loop:

    f(1);
    quit();
}