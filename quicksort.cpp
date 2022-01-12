/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>
#include <quicksort.h>

// Driver program to test header functions
int main()
{
  std::vector<int> my_vector{ 1, 2 };
  //          {1, 7, 8, 9, 10, 5};
  //          {1, 5, 8, 9, 10, 7};
  //          {1, 5, 8, 9, 10, 7};
  //          {1, 5, 7, 9, 10, 8};
  //          {1, 5, 7, 8, 10, 9};
  //          {1, 5, 7, 8, 9, 10};
  quickSort(my_vector, 0, my_vector.size()-1);
  printf("Sorted vector: \n");
  print_vector(my_vector);
  return 0;
}
