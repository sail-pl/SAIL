method f(x:box<int>){
    return
}
process Main(){
    
    var x : box<int>;
    var y : box<int>;
    x = box(1);
    f(x);
    y = x
}