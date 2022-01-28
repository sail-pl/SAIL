process Main(){

    var x : box<int>;
    {
        var y : box<int> = box(1)
        //;x = y  // Error the box is freed twice
        //<- here because of y
    }
    // <- here because of x
}