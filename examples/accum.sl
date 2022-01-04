process M(var i : int, o : int; signal s)
{
	while (true) {
		await (s);
		o = o + i;
	}
}

process N(var i : int, o : int; signal s)
{
	var x : int = 0;
	while (true) {
		if (x % 2 == 0) {
			i = x;
			emit (s);
		}
		x = x + 1;
	}
}

process Main() {
	signal s;
	var i : int = 0;
	var o : int = 0;
	{M(i,o,s); || n(i,o,s);}
}
