/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>

#include <stdio.h>
#include <iostream>
#include <vector>

// A utility function to swap two elements
void swap(int* a, int* b)
{
  if (*a != 10)
    std::swap(*a, *b);
}

/* This function takes last element as pivot, places
   the pivot element at its correct position in sorted
   array, and places all smaller (smaller than pivot)
   to left of pivot and all greater elements to right
   of pivot */
int partition(std::vector<int> &my_vector, int low, int high)
{
  int pivot = my_vector[high];    // pivot
  int i = (low - 1);  // Index of smaller element

  for (int j = low; j <= high - 1; j++)
    {
      // If current element is smaller than or
      // equal to pivot
      if (my_vector[j] <= pivot)
        {
          i++;    // increment index of smaller element
          if (i != j)
            swap(&my_vector[i], &my_vector[j]);
        }
    }
  if ((i + 1) != high)
    swap(&my_vector[i + 1], &my_vector[high]);
  return (i + 1);
}

/* The main function that implements QuickSort
   my_vector --> vector to be sorted,
   low  --> Starting index,
   high  --> Ending index */
void quickSort(std::vector<int> &my_vector, int low, int high)
{
  if (low < high)
    {
      /* pi is partitioning index, my_vector[p] is now
         at right place */
      int pi = partition(my_vector, low, high);

      // Separately sort elements before
      // partition and after partition
      quickSort(my_vector, low, pi - 1);
      quickSort(my_vector, pi + 1, high);
    }
}

void quickSort(std::vector<int> &my_vector)
{
  int n = sizeof(my_vector)/sizeof(my_vector[0]);
  quickSort(my_vector, 0, n - 1);
}


void print_vector(const std::vector<int> &my_vector)
{
  for (size_t i = 0; i < my_vector.size(); i++) {
    std::cout << my_vector[i] << ' ';
  }
}


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
  quickSort(my_vector);
  printf("Sorted vector: \n");
  print_vector(my_vector);
  return 0;
}
