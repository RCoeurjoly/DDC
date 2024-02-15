#include <iostream>
#include <numeric>
#include <vector>
#include <stdexcept>
#include <fstream>
#include <sstream>
#include <map>
#include <string>
#include <algorithm>
#include <stdio.h>
#include <memory>
#include <bits/stdc++.h>
#include <set>

void sum_vector_to_itself(std::vector<int> &my_vector) {
  std::transform (my_vector.begin(), my_vector.end(), my_vector.begin(), my_vector.begin(), std::plus<int>());
}

void multiply_vector_elements_by_two_to_the_size(std::vector<int> &my_vector) {
  for (auto index : my_vector) {
    sum_vector_to_itself(my_vector);
  }
}

int main() {
  std::vector<int> my_vector = {1,
    2,
    2,
    1,
    2,
    1,
    1,
    2,
    1,
    2,
    2,
    -1,
    0};
  multiply_vector_elements_by_two_to_the_size(my_vector);
  for (auto element : my_vector)
    std::cout << element << std::endl;
}
