def main():
    gdb.execute("source tests_demo.py")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("display low")
    gdb.execute("display high")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("c")

main()
