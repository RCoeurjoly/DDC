//Fibonacci Series using Recursion
#include<bits/stdc++.h>

int fib(int n)
{
  if (n <= 1)
    return n;
  return fib(n-1) + fib(n-2);
}

int main ()
{
  int n = 9;
  std::cout << fib(2) << std::endl;
  return 0;
}
