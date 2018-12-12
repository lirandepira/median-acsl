## median-acsl
The algorithm above calculates the median of an array while generating formal proof axioms.

- Algorithm: Median of an array
- Program to execute: Frama-c
- Proved goals:   40 / 40

### Introduction
The algorithm above calculates the median of an array. Steps to finding the median in plain C:
- As a pre-condition for calculation of the median in this example is the sorting process.
- A sorted array is checked whether it has an odd or even length
- If odd, the middle number is the median
- If even, the mean of the two middle numbers is the median

### Technical realisation in C
- The sort algorithm along with the axioms and requirements has been copy/pasted from an exercise in the class (with permission).
- The median function has been implemented easily

### Technical realisation in ACSL
1. Median axioms:
For the Axiomatic definition of median I assume that the three axioms must be achieved:

- Axiom 1: For a sorted array the median is the middle number
if sorted then a[size/2];

- Axiom 2: Swapping two values in an array does not change its median
if x == median(array1) && array2 == swap(array1, index1, index2) ==> x == median(array2);

- Axiom 3: If two arrays are the permutation of each other then they have the same median
if median(array1) == x && permutation(array1) == array2 ==> x == median(array2);
