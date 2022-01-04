struct point {
x : int;
y : int
}

enum option <A> {
 none ;
 some (A) 
}

struct node <A> {
 elem : A;
 tail : option <node <A>>
}
  
struct list <A> {
 head : option <node<A>>
}

method length (l : list<int>) : int is
{
  case l of 
  { cons(h) => return }
  { nil (x) => return };
  var x : int = 1;
  signal s;
  x = x;
  if x then if x then return else return 1;
  while x do return x;
  return
}

method cons() is {
  n = {elem : 1; next : 1};
  l = {head : n};
  return;
  return
}
