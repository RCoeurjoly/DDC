#include <quicksort.h>

int main(int argc, char **argv)
{
  std::vector<int> my_vector;
  for (int i=1; i < argc; ++i) {
    try {
      my_vector.push_back(std::stoi(argv[i]));
    }
    catch (std::invalid_argument const& ex) {
      std::cout << "Cannot convert argument in position " << i << " to int: " << ex.what() << '\n';
      return 1;
    }
  }
  print_vector(my_vector);
  quickSort(my_vector, 0, my_vector.size()-1);
  std::cout << "Sorted vector: \n";
  print_vector(my_vector);
  return 0;
}
