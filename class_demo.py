def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    gdb.execute("suspect-function Car::move(int const&, int const&)")

main()
