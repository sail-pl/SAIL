method min<T>(x : T, y : T) : T {
 if (x > y) return y 
  else return x
}
process Main() {
        print_int(min(3,4)); 
        print_newline ();
//      printf("%f\n", min(3.5,4.5));
}