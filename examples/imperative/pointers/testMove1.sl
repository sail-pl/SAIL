import test_utils
// Must fail, x moved twice
process Main {
Init:
Loop:

    
    var x : box<int>;
    var y : box<int>;
    var z : box<int>;
    //x = box(1);
    //y = x;
    //z = x;
    quit();
}
