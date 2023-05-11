process Main(){
	initialize () ;
    print_string("Hello World\n");
    ncurses_print("It ");
    ncurses_print("works !");
    ncurses_print("\n\n\n");
    double_print("Two print in ","one fuction");
    refr();
    waitevent();
    closewin()
}
