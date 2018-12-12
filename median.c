typedef unsigned int size_t;

/*@
predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
    b <= i < e && b <= j < e &&
    \at(a[i], L1) == \at(a[j], L2) && \at(a[j], L1) == \at(a[i], L2) &&
    \forall integer k; b <= k < e 
    && k != j && k != i ==> \at(a[k], L1) == \at(a[k], L2);

axiomatic Permutation{
  predicate permutation{L1,L2}(int* a, integer b, integer e)
        reads \at(*(a+(b .. e - 1)), L1), \at(*(a+(b .. e - 1)), L2);

  axiom reflexive{L1}: 
  \forall int* a, integer b,e ;
  permutation{L1,L1}(a, b, e);

  axiom swap{L1,L2}:
  \forall int* a, integer b,e,i,j ;
  swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);

  axiom transitive{L1,L2,L3}:
  \forall int* a, integer b,e ; 
  permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==> permutation{L1,L3}(a, b, e);
}
*/

/*@
    predicate sorted {L1} (int*a, integer b) =
    \forall integer k; k >=0 && k < b-1 ==> *(a+k) <= *(a+k+1);

    axiomatic Median{
        logic integer median {L1} (int* a, integer b)
        reads \at(*(a+(0 .. b - 1)), L1);

    axiom median_sorted{L1}:
    \forall int*a, integer b; sorted(a, b) ==> median(a, b) == a[b/2];

    axiom median_middle{L1, L2}:
    \forall int*a, integer b, c, d;
    swap_in_array{L1,L2}(a, 0, b, c, d) ==> median{L1}(a, b) == median{L2}(a,b);

    axiom median_transitive{L1, L2}:
    \forall int*a, integer b;
    permutation{L1, L2}(a,0,b) ==> median{L1}(a,b) == median{L2}(a,b);
    }
*/

/*@
  requires \valid(a + (beg..end-1));
  requires beg < end;
  ensures beg <= \result < end;
  ensures \forall size_t i; beg <= i < end ==> a[i] >= a[\result];
  ensures \old (beg) == beg;
  ensures \old (end) == end;
  assigns \nothing;
 */
size_t min_idx_in(int* a, size_t beg, size_t end){
  size_t min_i = beg;
  /* invariant: la valeur stockÃ©e Ã  l'indice min_i est <= aux valeurs stockÃ©es aux indices entre beg et i */
  /*@ loop assigns min_i,i;
    loop invariant beg <= i <= end;
    loop invariant beg <= min_i < end;
    loop invariant \forall size_t j; beg <= j < i  ==> a[j] >= a[min_i]; 
   */
  for(size_t i = beg+1; i < end; ++i)
    if(a[i] < a[min_i]) min_i = i;
return min_i;
}

/* Ã©change les valeurs des deux pointeurs */
/*@
  requires \valid(p);
  requires \valid(q);
  ensures *p == \old(*q) && *q == \old(*p);
  assigns *p, *q;
 */
void swap(int* p, int* q){
  int tmp = *p; *p = *q; *q = tmp;
}

/* trie le tableau a[beg,end-1].
 SpÃ©cifier que le tableau Ã  la sortie est une permutation du tableau en entrÃ©e.
 SpÃ©cifier que le tableau en sortie est triÃ©.
*/
/*@
  requires \valid(a + (beg..end-1));
  ensures \forall size_t i; \forall size_t j; 
      beg <= i <= j < end ==> a[i] <= a[j];
  ensures permutation{Pre,Post}(a,beg,end);
  assigns a[beg..end-1];
 */
void sort(int* a, size_t beg, size_t end){
  /* si le tableau est vide, on ne fait rien */
  if(end <= beg)
    return;

label:
  /* Ã  l'Ã©tape i, le tableau a[beg,i-1] est triÃ©
   de plus les Ã©lÃ©ments de a[beg,i-1] sont tous infÃ©rieurs aux Ã©lÃ©ments de a[i..end]
*/
  /*@ loop assigns i,a[beg..end-1];
    loop invariant beg <= i <= end;
    loop invariant \forall size_t i0; \forall size_t i1; 
       beg <= i0 < i <= i1 < end ==> a[i0] <= a[i1];  
    loop invariant \forall size_t i0; \forall size_t i1;
       beg <= i0 <= i1 < i ==> a[i0] <= a[i1];
    loop invariant permutation{label,Here}(a,beg,end);
   */
for(size_t i = beg ; i < end ; ++i){
    /* il faut garantir que min_idx_in ne modifie pas i */
    size_t imin = min_idx_in(a, i, end);
    debut_for:;
    /*@ assert beg <= imin < end; */
    swap(a+i, a+imin);
    /*@ assert swap_in_array{debut_for,Here}(a,beg,end,i,imin);*/
}
}

/* Specification: the code below calculates the median
of any array of integers */
/*
C for compilation purposes
*/
/*int main (int argc, const char * argv[]){
    int arr[] = {4, 18, 29, 23};
    int length = sizeof(arr)/sizeof(int);

    int returnedValue = median(arr, length);
    printf("Median is %d", returnedValue);
    return 0;
}*/

/*@ 
  requires length > 0;
  requires \valid(t + (0..length-1)); 
*/

int median (int* t, int length){
    sort(t, 0, length);

    if (length % 2 == 0) {
        return ((t [length/2] + t [length/2-1]) / 2.0);
    } else {
        return t [length/2];
    }
}