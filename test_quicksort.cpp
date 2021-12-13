/* C implementation QuickSort */
#include <stdio.h>
#include <iostream>
#include <quicksort.h>
#include <algorithm>
#include <cassert>

// Driver program to test above functions
int main()
{
  int arr[6] = {0, 0, 0, 0, 0, 0};
  const int n = 6;
  bool correct = true;
  for (int a = 0; a <= 9; a ++) {
    for (int b = 0; b <= 9; b ++) {
      for (int c = 0; c <= 9; c ++) {
        for (int d = 0; d <= 9; d ++) {
          for (int e = 0; e <= 9; e ++) {
            for (int f = 0; f <= 9; f ++) {
              arr[0] = a;
              arr[1] = b;
              arr[2] = c;
              arr[3] = d;
              arr[4] = e;
              arr[5] = f;
              quickSort(arr, 0, n-1, "bug");
              correct &= !std::is_sorted(arr, arr + 6);
              print_array(arr);
              printf("\n");
            }
          }
        }
      }
    }
  }
  exit(correct);
}
