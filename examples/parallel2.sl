process Main(){

    print_string("A\n");
    signal s; watching(s){emit (s); signal s; when(s){}}
    print_string("C\n")
    ||
    print_string("B\n");
    print_string("D\n")
}


    