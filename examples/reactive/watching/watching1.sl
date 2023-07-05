import test_utils
process Main {
Init:
Loop:

    signal s;
    {
        watching s {signal s2; when s2 {}}; print_string("Instant 2\n")
        ||
        emit s; print_string("Instant 1\n")
    };
    exit(0);
}