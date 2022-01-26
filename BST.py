def main():
    gdb.execute("del")
    gdb.execute("source declarative_debugger.py")
    gdb.execute("start")
    gdb.execute("suspect-function nodeBST::nodeBST(int)")
    gdb.execute("suspect-function nodeBST::nodeBST()")
    gdb.execute("suspect-function nodeBST::traverseInOrder(nodeBST*)")
    gdb.execute("suspect-function nodeBST::insertFunc(nodeBST*, int)")
    gdb.execute("suspect-function main()")
    gdb.execute("set pagination off")
    gdb.execute("start-declarative-debugging-session")

main()
