extern "c" {
	method printf(s : string ...);
	method initscr();
	method printw(s : string)
}

method print_int(v : int)  {
	printf("%i", v)
}

method print_string(v : string)  {
        printf("%s", v)
}

method print_newline() {
	printf("\n")
}

method initialize() {
	initscr()
}

method ncurses_print(s : string) {
	printw(s)
}

method double_print(s1 : string , s2 : string){
	printw(s1);
	printw(s2)
}
