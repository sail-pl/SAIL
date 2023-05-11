extern "c" {
	method refresh();
	method getch();
	method endwin()
}

method refr() {
	refresh()
}

method waitevent(){
	getch()
}

method closewin(){	
	endwin()
}
