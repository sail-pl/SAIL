enum option<A> {
	None,
	Some(A)
}

struct list<A> {
	head : option<box<node<A>>>
}

struct node<T> {
	elem : A,
	next : option<box<node<A>>>
}

method length<A>(l : &list<A>) : int {
	case (&l.head) {
		None : return 0;
		Some(node) : return 1 + length(node.next);
	}
}

method push<A>(l : &mut list<A>, elem : A) {
	var node : node<int> = {elem : elem; next : take(l.head)};
	l.head = some(box(node));
}

process Pause(){
	signal s1;
	watching(s1){emit(s1); signal s2; when(s2){}}
}

process M(var x : &mut list<int>, y : &int ; signal s1,s2){
	watching(s2){
		when(s1) push(x, *y);
	}
	return;
}

process N(var x : &mut list<int>, y : &mut int; signal s1, s2){
	var i : int = 0;
	while(i < 10){
		emit(s1); 
		i = i + 1; 
		*y = i; 
		Pause();
	}
	emit(s2);
}

process Main(){
	var x : &mut list<int> = {head : None};
	var y : &mut int = 0;
	signal s1;
	signal s2;	
	{M(x, y, s1, s2); || N(x, y, s1, s2);}
}