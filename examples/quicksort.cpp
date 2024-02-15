#include <quicksort.h>

int main(int argc, char **argv)
{
  std::vector<int> my_vector{ 10, 7, 8, 9, 1, 5 };
  quickSort(my_vector, 0, my_vector.size()-1);
  std::cout << "Sorted vector: " << std::endl;
  print_vector(my_vector);
  return 0;
}