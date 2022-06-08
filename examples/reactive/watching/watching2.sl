process Main(){
    signal s1;
    {
        emit s1
        ||
        when s1 {print_string ("A\n")};
        signal s2; watching s2 {emit s2; signal s3; when s3 {}};
        when s1 {print_string ("B\n")}
    }
}
