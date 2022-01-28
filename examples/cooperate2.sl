process Main(){
    signal s; watching s { emit  s ; signal s; when s {}}
}
