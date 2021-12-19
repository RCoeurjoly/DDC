def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    gdb.execute("suspect-function quickSort(std::vector<int, std::allocator<int> >&, int, int, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >)")
    gdb.execute("suspect-function swap(int*, int*)")
    gdb.execute("suspect-function partition(std::vector<int, std::allocator<int> >&, int, int)")
    gdb.execute("final-point print_vector(std::vector<int, std::allocator<int> >const &)")

main()
