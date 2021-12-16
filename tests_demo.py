def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    gdb.execute("save-correct-function quickSort(std::vector<int, std::allocator<int> >&, int, int, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >)")
    gdb.execute("save-correct-function swap(int*, int*)")
    gdb.execute("save-correct-function partition(std::vector<int, std::allocator<int> >&, int, int)")
    gdb.execute("start")

main()
