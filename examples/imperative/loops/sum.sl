method sumTo(n : int) : int{
    var mut res : int = 0;
    var mut cpt : int = 0;
    while (cpt < 10){
        res = res + cpt;
        cpt = cpt+1
    }
    return res
}

process Main(){
    print_int(sumTo(10));
    print_newline();
}
