#include <quicksort.h>
#include <algorithm>
#include <cassert>

int main()
{
  std::vector<int> my_vector{ 0, 0, 0, 0, 0, 0 };
  for (int i = 0; i <= 9; i++) {
    my_vector[0] = rand() % 9 + 1;
    my_vector[1] = rand() % 9 + 1;
    my_vector[2] = rand() % 9 + 1;
    my_vector[3] = rand() % 9 + 1;
    my_vector[4] = rand() % 9 + 1;
    my_vector[5] = rand() % 9 + 1;
    quickSort(my_vector, 0, my_vector.size()-1, "");
    if (!std::is_sorted(my_vector.begin(), my_vector.end()))
      return 1;
  }
  return 0;
}
