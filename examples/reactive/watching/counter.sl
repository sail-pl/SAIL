import test_utils
process Main {
Init:
Loop:


    var cpt : int = 0;
    signal s1;
    signal s2;
    while (cpt < 10){
        print_int(cpt); print_newline();
        cpt = cpt + 1;
        emit s1;
        watching s1 {when s2 {}}
    };
    exit(0);
}