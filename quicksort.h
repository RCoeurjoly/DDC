/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>

// A utility function to swap two elements
void swap(int* a, int* b)
{
  int t = *a;
  if (t != 10) {
  // if (true) {
    *a = *b;
    *b = t;
  }
}

/* This function takes last element as pivot, places
   the pivot element at its correct position in sorted
   array, and places all smaller (smaller than pivot)
   to left of pivot and all greater elements to right
   of pivot */
int partition (int arr[6], int low, int high)
{
  int pivot = arr[high];    // pivot
  int i = (low - 1);  // Index of smaller element

  for (int j = low; j <= high- 1; j++)
    {
      // If current element is smaller than or
      // equal to pivot
      if (arr[j] <= pivot)
        {
          i++;    // increment index of smaller element
          swap(&arr[i], &arr[j]);
        }
    }
  swap(&arr[i + 1], &arr[high]);
  return (i + 1);
}

/* The main function that implements QuickSort
   arr[] --> Array to be sorted,
   low  --> Starting index,
   high  --> Ending index */
void quickSort(int arr[6], int low, int high, std::string gdb_bug="")
{
  if (low < high)
    {
      /* pi is partitioning index, arr[p] is now
         at right place */
      int pi = partition(arr, low, high);

      // Separately sort elements before
      // partition and after partition
      quickSort(arr, low, pi - 1);
      quickSort(arr, pi + 1, high);
    }
}

template<typename T, size_t n>
void print_array(T const(& arr)[n])
{
  for (size_t i = 0; i < n; i++) {
    std::cout << arr[i] << ' ';
  }
}
