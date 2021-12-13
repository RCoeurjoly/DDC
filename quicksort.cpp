/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>
#include <quicksort.h>

template<typename T, size_t n>
void print_array(T const(& arr)[n])
{
  for (size_t i = 0; i < n; i++) {
    std::cout << arr[i] << ' ';
  }
}

// Driver program to test header functions
int main()
{
  int arr[6] = {10, 7, 8, 9, 1, 5};
  //          {1, 7, 8, 9, 10, 5};
  //          {1, 5, 8, 9, 10, 7};
  //          {1, 5, 8, 9, 10, 7};
  //          {1, 5, 7, 9, 10, 8};
  //          {1, 5, 7, 8, 10, 9};
  //          {1, 5, 7, 8, 9, 10};
  int n = sizeof(arr)/sizeof(arr[0]);
  quickSort(arr, 0, n-1, "bug");
  printf("Sorted array: \n");
  //foo(10);
  print_array(arr);
  return 0;
}
