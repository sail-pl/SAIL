import test_utils
method f(x:box<int>){
    return
}
process Main {
Init:
Loop:

    
    var x : box<int>;
    var y : box<int>;
    x = box(1);
    f(x);
    y = x;
    exit(0);
}