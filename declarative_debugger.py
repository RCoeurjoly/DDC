import os
import sys

class DebuggingSession:
    def __init__(self):
        self.nodes = []
        self.started = False
        self.finished = False
    def __repr__(self):
        nodes = ""
        for node in self.nodes:
            nodes += repr(node) + "\n"
        return nodes + "Started: " + str(self.started) + "\nFinished: " + str(self.finished)
    def start(self):
        self.started = True
    def finish(self):
        self.finished = True

class CommandFinishSession(gdb.Command):
  """Set breakpoint for ending debugging session"""
  def __init__ (self):
      super (CommandFinishSession, self).__init__ ("finish-debugging-session", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
      global my_debugging_session
      my_debugging_session.finished = True

CommandFinishSession()

class Node:
    def __init__(self, frame, arguments=[], global_variables=[], object_state=None):
        self.frame = frame
        # self.frame_hash = hash(frame)
        self.name = frame.name()
        self.arguments_when_called = arguments
        self.arguments_when_returning = []
        self.global_variables_when_called = global_variables
        self.global_variables_when_returning = []
        self.object_state_when_called = object_state
        self.object_state_when_returning = None
        self.return_value = None
        self.children = []

    def __repr__(self):
        str_children = ""
        for node in self.children:
            str_children += "\n\t" + repr(node)
        return self.name + str_children

    def finish(self, arguments=None, global_variables=None, object_state=None, return_value=None):
        self.arguments_when_returning = arguments
        self.global_variables_when_returning = global_variables
        self.object_state_when_returning = object_state
        self.return_value = return_value

    def adopt(self, children_node):
        self.children.append(children_node)

class SetBreak(gdb.Breakpoint):
    def __init__(self, function, final=False):
        gdb.Breakpoint.__init__(self, function)
        self.final = final
        if (final):
            self.commands = "finish-debugging-session"
        else:
            self.commands = "add-node-to-session\nc"
        self.silent = False

    def stop(self):
        return True # stop the execution at this point

class CommandAddNodeToSession(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__ (self):
        super (CommandAddNodeToSession, self).__init__ ("add-node-to-session", gdb.COMMAND_USER)

    def invoke (self, arg, from_tty):
        global my_debugging_session
        # Variable: Symbol.is_argument
        arguments = [symbol for symbol in gdb.selected_frame().block() if symbol.is_argument]
        my_node = Node(gdb.selected_frame(), arguments)
        print("Position is: " + str(add_node_to_list(my_debugging_session.nodes, my_node, [])))
        MyFinishBreakpoint()

CommandAddNodeToSession()

def add_node_to_list(nodes, node, position):
    if nodes == [] or not nodes[-1].frame.is_valid():
        position.append(len(nodes))
        nodes.append(node)
        return position
    else:
        position.append(len(nodes)-1)
        return add_node_to_list(nodes[-1].children, node, position)

def get_parent_frames(node):
    parents = []
    aux_node = node.frame.older()
    while aux_node is not None:
        parents.append(aux_node)
    return parents

class CommandSuspectFunction(gdb.Command):
  """Set breakpoint for ending debugging session"""

  def __init__ (self):
    super (CommandSuspectFunction, self).__init__ ("suspect-function", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
    SetBreak(arg, False)

CommandSuspectFunction()

class CommandFinalBreakpoint(gdb.Command):
  """Set breakpoint for ending debugging session"""

  def __init__ (self):
    super (CommandFinalBreakpoint, self).__init__ ("final-point", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
    SetBreak(arg, True)

CommandFinalBreakpoint()

class SetBreakpoint(gdb.Command):
    """Set breakpoint on function or method"""
    def __init__ (self):
        super (SetBreakpoint, self).__init__ ("set-breakpoint", gdb.COMMAND_USER)

    def invoke (self, arg, from_tty):
        return

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
    print(my_debugging_session)

PrintNodes()

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
    # def __init__(self, frame=gdb.newest_frame(), internal=True):
    #     super(MyFinishBreakpoint, self).__init__(frame, internal)
    #     self.associated_frame = frame
    def stop (self):
        global my_debugging_session
        last_node = get_last_node(my_debugging_session.nodes)
        #print("Nodo que hemos finalizado: " + last_node.name)
        print("Codigo de retorno: " + str(self.return_value))
        # print("normal finish")
        self.commands = "c"
        return True
    def out_of_scope(self):
        print("abnormal finish")

def get_node_with_frame(nodes, frame):
    if not nodes:
        return None
    else:
        return None


def get_last_node(nodes):
    if nodes == []:
        print("This should never happen")
        return None
    else:
        if nodes[-1].children == []:
            print("yohooo")
            return nodes[-1]
        else:
            return get_last_node(nodes[-1].children)

def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    gdb.execute("suspect-function quickSort")
    gdb.execute("suspect-function swap(int*, int*)")
    gdb.execute("suspect-function partition(int*, int, int)")
    gdb.execute("final-point quicksort.cpp:81")
    gdb.execute("start")
    gdb.execute("c")
    gdb.execute("c")

my_debugging_session = DebuggingSession()

main()
