import test_utils
process Main {
Init:
Loop:


    {
        var x : box<int> = box(3);
            print_string("done\n")
    }
    print_string("done\n");
    exit(0);
}