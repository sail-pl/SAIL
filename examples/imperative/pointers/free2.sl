import print_utils
process Main (){
    
    var x : int = 0;
    while (x < 1){
        x = x + 1;
        var y : box<int> = box(1);
        drop(y)
    }

}