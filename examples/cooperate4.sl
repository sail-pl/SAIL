process Main(){
    signal s;
    {
        when s {print_string("Hello World\n")}
    ||
        signal s3; watching s3 {emit  s3 ;signal s4; when s4 {}}
        emit s
    }
}