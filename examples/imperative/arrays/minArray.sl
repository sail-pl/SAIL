import print_utils
process Main(){
    var mut a : array<int;10> = [6,57,23,2,5,6,7,10,13,5];
    var mut res : int = 0;
    var mut cpt : int = 1;
    while (cpt < 10) {
        if (a[cpt] < a[res]) 
            res = cpt;
        cpt = cpt + 1
    }
    print_int (a[res]); print_newline()
}
