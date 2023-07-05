import test_utils
method f(x:box<int>, y:box<int>){

}
process Main {
Init:
Loop:

    
    var x : box<int>;
    x = box(1);
    f(x,x);
    exit(0);
}