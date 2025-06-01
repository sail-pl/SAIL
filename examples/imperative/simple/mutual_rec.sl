import test_utils

method a(x : int) : int {
 if (x <= 1) {
 	return 1
 } else {
 return b(x+2);
 }
}

method b(x : int) : int {
	return a(x - 3) + 4
}


process Main {
	Run:
        print_int(a(12)); print_newline();
        quit();
}
