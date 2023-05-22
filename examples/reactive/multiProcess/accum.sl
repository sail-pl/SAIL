import print_utils
process M(var i : int, o : int; signal s)
{
	while (true) {
		await s;
		o = o + i;
	}
}

process N(var i : int, o : int; signal s)
{
	var x : int;
	x = 0;
	while (true) {
		if (x % 2 == 0) {
			i = x;
			emit s;
		}
		x = x + 1;
	}
}

process Main() {
	signal s;
	var i : int;
	var o : int;
	i = 0;
	o = 0;
	{ M(i,o,s) || N(i,o,s)}
} 
