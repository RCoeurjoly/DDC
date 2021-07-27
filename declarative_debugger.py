import os
import sys

class StartDeclarativeDebuggingSession(gdb.Command):
  """Set breakpoint on setField from Quickfix. It takes the tag number as argument"""

  def __init__ (self):
    super (StartDeclarativeDebuggingSession, self).__init__ ("start-declarative-debugging-session", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
    return

class PrintNodes(gdb.Command):
  """Print nodes of declarative debugging session"""

  def __init__ (self):
    super (PrintNodes, self).__init__ ("print-nodes", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
    return

class PrintNode(gdb.Command):
  """Print node of declarative debugging session"""

  def __init__ (self):
    super (PrintNode, self).__init__ ("print-node", gdb.COMMAND_USER)

  def invoke (self, frame_id, from_tty):
    return

class SaveStartNode(gdb.Command):
  """Save the info at the moment a node is called in declarative debugging session"""

  def __init__ (self):
    super(SaveStartNode, self).__init__ ("save-start-node", gdb.COMMAND_USER)

  def invoke (self, frame_id, from_tty):
    frame = gdb.selected_frame() # Use the current frame
    return frame

class SaveReturningNode(gdb.Command):
  """Save the info at the moment a node is returning in declarative debugging session"""

  def __init__ (self):
    super(SaveReturningNode, self).__init__ ("save-returning-node", gdb.COMMAND_USER)

  def invoke (self, frame_id, from_tty):
    return


class MyFinishBreakpoint (gdb.FinishBreakpoint):
    def stop (self):
        print ("normal finish")
        return True
    def out_of_scope ():
        print ("abnormal finish")

def main():
    gdb.execute("del")
    gdb.execute("break quickSort")
    gdb.execute("start")
    gdb.execute("c")
    gdb.execute("c")
    frame_first_quicksort = gdb.selected_frame() # Use the current frame
    #gdb.execute("dis")
    MyFinishBreakpoint()
    #gdb.execute("c")
    #frame_second_quicksort = gdb.selected_frame()
    #print(frame_second_quicksort.older() == frame_first_quicksort)
    #print(frame_second_quicksort == frame_first_quicksort)

#main()
