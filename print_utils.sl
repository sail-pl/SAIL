extern "c" {
	method printf(s : string ...)
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
