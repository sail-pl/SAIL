import print_utils
process Main(){
    signal s1;
    signal s2;
    var cpt : int = 0;
    var n : int = 5;
    {
        while(cpt < n){
            emit s2;
            when s1 {print_string("A\n")}
            signal s; watching s {emit s;signal s; when s {}}
        }
    ||
        while(cpt < n){
            when s2 {print_string("B\n")}
            signal s; watching s {emit s;signal s; when s {}}
            emit s1
        }
    ||
        while(cpt < n){
            cpt = cpt + 1;
            signal s; watching s {emit s;signal s; when s{}}
        }
    }
}