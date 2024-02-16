def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    gdb.execute("suspect-function reverse_int(int)")
    gdb.execute("suspect-function reverse_int(int, int, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >)")
    gdb.execute("suspect-function trivial(int)")

main()
