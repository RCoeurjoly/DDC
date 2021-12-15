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






bool result = false;

std::vector<bool> my_vector = {true, false, true};

bool my_xor(bool a, bool b) {
  return a ^ b;
}

bool odd_parity(std::vector<bool> my_vector) {
  bool result = false;
  for (auto my_bool : my_vector)
    result = my_xor(result, my_bool);
  return result;
}

int main() {
  std::vector<bool> my_vector = {true,
    false,
    false,
    true,
    false,
    true,
    true,
    false,
    true,
    false,
    false,
    true,
    true};
  std::cout << odd_parity(my_vector) << std::endl;
}

