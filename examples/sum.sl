method sumTo(n : int) : int{
    var res : int = 0;
    var cpt : int = 0;
    while (cpt < 10){
        res = res + cpt;
        cpt = cpt+1;
    }
    return res;
}

process Main(){
    var x : int = sumTo(10);
}