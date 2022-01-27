process Main(){
    {
        signal s1;
        {
        {
            var cpt : int = 0;
            signal s2;
            signal s3;
            watching (s1) {
                while(true){
                   print_string("P1 : ");
                   print_int(cpt); print_newline();
                    cpt = cpt + 1;
                    watching (s2) {emit (s2); when (s3){}}
                }
            }
        }
        ||
        {
            var cpt : int = 0;
            signal s4;
            signal s5;
            while (cpt < 10){
                print_string("P2 : ");
                print_int(cpt); print_newline();
                cpt = cpt + 1;
                watching (s4) {emit (s4); when (s5){}}
            }
            emit(s1);           
        }
    }
    }
}