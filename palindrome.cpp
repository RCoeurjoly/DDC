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

int trivial(int a) {
  return a;
}

int reverse_int(int a, int t, std::string gdb_bug="") {
  if (a == 0)
    return trivial(t);
  t = (t * 10) + (a % 10);
  return reverse_int(a / 10, t);
}


int reverse_int(int a) {
  return reverse_int(a, 0);
}

int main() {
  int n = 111111111;
  int result = reverse_int(n);
  if (result == n)
    std::cout << "Number "<< n <<" is a palindrome" << std::endl;
  else
    std::cout << "Number "<< n <<" is not a palindrome"<< std::endl;
  return 0;
}
