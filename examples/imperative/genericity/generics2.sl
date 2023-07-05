import test_utils
method add<T>(n1 : T, n2 : T) : T {
	var x : T = n1;
	var y : T = n2;

	return x + y;
}

process Main {
	var x : int = add(2,3);
	var y : float =	add(2.,4.);

//error	var b : bool = add(true,false);
//error	var c : char = add('a','\n');

	print_int(x);
	print_newline();
//        printf("%f\n", y);

//      printf("%b\n", b);
//	printf("%c\n", c);
    exit(0);
}
