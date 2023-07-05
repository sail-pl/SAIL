import test_utils
process Main {
Init:
Loop:


    var x : box<int>;
    {
        var y : box<int> = box(1);
        x = y
        // Ok, the content of y was tagged as moved, no free here
    }
    // OK, the pointer is freed once here;
    exit(0);
}