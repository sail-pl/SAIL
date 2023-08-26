import test_utils
process Main {
Init:
Loop:

  var x : box<int> = box(3);  
  print_int(*x);
    quit();
}