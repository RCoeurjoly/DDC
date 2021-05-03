import os
import sys

def main():
    gdb.execute("break quickSort")
    gdb.execute("r")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("quit")

main()
