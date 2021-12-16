/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>
#include <quicksort.h>

// Driver program to test header functions
int main()
{
  std::vector<int> my_vector{ 10, 7, 8, 9, 1, 5 };
  //          {1, 7, 8, 9, 10, 5};
  //          {1, 5, 8, 9, 10, 7};
  //          {1, 5, 8, 9, 10, 7};
  //          {1, 5, 7, 9, 10, 8};
  //          {1, 5, 7, 8, 10, 9};
  //          {1, 5, 7, 8, 9, 10};
  int n = sizeof(my_vector)/sizeof(my_vector[0]);
  quickSort(my_vector, 0, n-1, "bug");
  printf("Sorted vector: \n");
  print_vector(my_vector);
  return 0;
}
