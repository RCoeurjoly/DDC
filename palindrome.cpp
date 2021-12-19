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

int palindrome(int a, int t, std::string gdb_bug="") {
  if (a == 0)
    return t;
  t = (t * 10) + (a % 10);
  return palindrome(a / 10, t);
}


int palindrome(int a) {
  return palindrome(a, 0);
}

int main() {
  int n = 11;
  int result = palindrome(n);
  if (result == n)
    std::cout << "Number "<< n <<" is a palindrome" << std::endl;
  else
    std::cout << "Number "<< n <<" is not a palindrome"<< std::endl;
  return 0;
}
