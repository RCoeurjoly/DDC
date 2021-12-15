def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    gdb.execute("suspect-function quickSort(int*, int, int, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >)")
    gdb.execute("suspect-function swap(int*, int*)")
    gdb.execute("suspect-function partition(int*, int, int)")
    gdb.execute("final-point print_array<int, 6ul>(int const (&) [6ul])")
    gdb.execute("start")
    # gdb.execute("start-declarative-debugging-session")

main()
