import print_utils
method f(x:box<int>, y:box<int>){

}
process Main(){
    
    var x : box<int>;
    x = box(1);
    f(x,x)
}