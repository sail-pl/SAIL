import test_utils
process Main {
Init:
Loop:

    signal s1;
    {
        var cpt : int = 0;
        watching s1 {
            while(true){
                print_string("P1 : ");
                print_int(cpt); print_newline();
                cpt = cpt + 1;
                signal s; watching s {emit s; signal s; when s{}}
            }
        }
    ||
        var cpt : int = 0;
        while (cpt < 10){
            print_string("P2 : ");
            print_int(cpt); print_newline();
            cpt = cpt + 1;
            signal s; watching s { emit s; signal s; when s{}}
        }
        emit s1       
    };
    exit(0);
}