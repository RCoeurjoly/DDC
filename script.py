import os
import sys

def main():
    gdb.execute("break quickSort")
    gdb.execute("start")
    gdb.execute("c")
    gdb.execute("c")
    gdb.execute("c")
    frame = gdb.selected_frame() # Use the current frame
    print(id(frame))
    print(frame.address())
    print(frame.older().pc())
    print(frame.older().older().pc())
    #args = [arg for arg in frame.block() if arg.is_argument]
    #print(args)

main()
