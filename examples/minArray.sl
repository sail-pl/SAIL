process Main(){
    var a : array<int> = [6,57,23,2,5,6,7,10,13,5];
    var res : int = 0;
    var cpt : int = 1;
    while (cpt < 10) {
        if (a[cpt] < a[res]) 
            res = cpt;
        cpt = cpt + 1
    }
    print_int (a[res]); print_newline()
}