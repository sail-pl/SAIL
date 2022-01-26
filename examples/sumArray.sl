process Main(){
    var a : array<int> = [1,2,3,4,5,6,7,8,9,10];
    print_string("Hello World\n"); 

    var res : int = 0;
    var cpt : int = 0;
    print_string("Hello\n");
    while (cpt < 10) {
        res = res + a[cpt];
        cpt = cpt + 1;
    }
    print_int (res); print_newline();
    print_string("Hello\n");
}