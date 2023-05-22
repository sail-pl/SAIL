import print_utils

method getMin<T> (a : array<T;5>) : T {

 var res : int = 0;
 var cpt : int = 1;

    while (cpt < 5) {
        if (a[cpt] < a[res])
            res = cpt;
  
        cpt = cpt + 1
    }
  return a[res]; 

}



process Main(){
	var a : array<int;5> = [6,57,23,2,5];
	var c : array<float;5> = [1.5,2.1,6.2,0.1,6.5];
	a[1] = 5;

	printf("%i\n", getMin(a));
	printf("%f\n", getMin(c));
}
