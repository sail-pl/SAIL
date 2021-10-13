struct point {
x : int;
y : int;
};

struct patchwork {
x : float;
y : bool;
z : char;
t : int[10][10];
u : point;
v : point<A>;
w : &int;
s : &mut int; 
};

enum option <A> {
 none : null ;
 some : A ;
};

struct node <A> {
 elem : A;
 tail : option <node <A>>;
};
  
struct list <A> {
 head : option <node<A>>;
};

struct pair <A,B> {
 a : A;
 b : B;
};

struct tree <A> {
 value : A;
 left : tree <A>;
 right : tree <A>;
};

method length (l : list<int>) : int {
  /*case (l){
    cons h t { 
      return;
    }
    nil {
      return;
    }
    }*/
  var x : int = 1;
  sig s;
  x = x;
  if x {return 1};
  while x {return x};
  return
}

method cons() {
  /*  n = {elem = 1; next = nil};
      l = {head = n;};*/
  return;
  return
}
