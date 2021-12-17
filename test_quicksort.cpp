/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>
#include <quicksort.h>
#include <algorithm>
#include <cassert>

// Driver program to test above functions
int main()
{
  std::vector<int> my_vector{ 0, 0, 0, 0, 0, 0 };
  const int n = 6;
  bool correct = true;
  for (int i = 0; i <= 99; i++) {
    my_vector[0] = rand() % 9 + 1;
    my_vector[1] = rand() % 9 + 1;
    my_vector[2] = rand() % 9 + 1;
    my_vector[3] = rand() % 9 + 1;
    my_vector[4] = rand() % 9 + 1;
    my_vector[5] = rand() % 9 + 1;
    print_vector(my_vector);
    std::cout << std::endl;
    quickSort(my_vector, 0, n-1, "bug");
    correct = correct && std::is_sorted(my_vector.begin(), my_vector.end());
    std::cout << correct << std::endl;
    print_vector(my_vector);
    printf("\n");
    if (!correct)
      exit(1);
  }
  return correct;
}
