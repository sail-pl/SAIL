process Main(){
    signal s1;
    signal s2;
    {
        {
            print_string("P1a\n");
            when(s1){}
            print_string("P1b\n");
            emit(s2);

            watching(s1){signal s3; when(s3){}}
        }
        ||
        {
            print_string("P2a\n");
            emit(s1);
            when(s2){}
            print_string("P2b\n");
            signal s3;
            watching(s2){ when(s3){}}
        }
    }
}