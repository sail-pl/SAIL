import test_utils
process Main {
Init:
Loop:

  
  var x : box<int>;
  x = box(3);
  x = box(1);
  print_string("done\n");
    exit(0);
}