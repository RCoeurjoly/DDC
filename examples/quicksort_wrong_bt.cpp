#include <stdio.h>
#include <iostream>
#include <stdio.h>
#include <iostream>
#include <vector>

void swap(int* a, int* b)
{
  if (*a != 10)
    std::swap(*a, *b);
}

int partition(std::vector<int> &my_vector, int low, int high)
{
  int pivot = my_vector[high];    // pivot
  int i = (low - 1);  // Index of smaller element

  for (int j = low; j <= high - 1; j++)
    {
      if (my_vector[j] <= pivot)
        {
          i++;
          if (i != j)
            swap(&my_vector[i], &my_vector[j]);
        }
    }
  if ((i + 1) != high)
    swap(&my_vector[i + 1], &my_vector[high]);
  return (i + 1);
}

void quickSort(std::vector<int> &my_vector, int low, int high)
{
  if (low < high)
    {
      int pi = partition(my_vector, low, high);
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

int main()
{
  std::vector<int> my_vector{ 10, 7, 8, 9, 1, 5 };
  quickSort(my_vector);
  //printf("Sorted vector: \n");
  //print_vector(my_vector);
  //return 0;
}
