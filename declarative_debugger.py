import os
import sys
from rich.tree import Tree
from rich import print

class DebuggingSession:
    def __init__(self):
        self.children = []
        self.started = False
        self.finished = False
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
        self.arguments_on_entry = arguments
        args = ""
        for argument in self.arguments_on_entry:
            args += argument.print_name + " = " + str(argument.value(self.frame)) + ", "
        self.arguments_on_entry_str = args
        self.arguments_when_returning = []
        self.arguments_when_returning_str = ""
        self.global_variables_on_entry = global_variables
        self.global_variables_when_returning = []
        self.object_state_on_entry = object_state
        self.object_state_when_returning = None
        self.return_value = None
        self.children = []

    def get_tree(self):
        tree = Tree(self.name + ": args: " + self.arguments_on_entry_str)
        for child in self.children:
            tree.add(child.get_tree())
        return tree

    def finish(self, arguments=None, global_variables=None, object_state=None, return_value=None):
        self.arguments_when_returning = arguments
        args = ""
        for argument in self.arguments_when_returning:
            args += argument.print_name + " = " + str(argument.value(self.frame)) + ", "
        self.arguments_when_returning_str = args
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
            self.commands = ("add-node-to-session\n"
                             "c")
        self.silent = False

    def stop(self):
        return True # stop the execution at this point


class SaveReturningNode(gdb.Command):
  """Save the info at the moment a node is returning in declarative debugging session"""

  def __init__ (self):
    super(SaveReturningNode, self).__init__ ("save-returning-node", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
      gdb.execute("reverse-step")
      global my_debugging_session
      arguments = [symbol for symbol in gdb.newest_frame().block() if symbol.is_argument]
      my_node = get_node_from_frame(my_debugging_session.children, gdb.newest_frame())
      my_node.finish(arguments=arguments)
      #my_node.arguments_when_returning = [1, 2]
      gdb.execute("n")
      #gdb.execute("c")
      return

SaveReturningNode ()

class CommandAddNodeToSession(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__ (self):
        super (CommandAddNodeToSession, self).__init__ ("add-node-to-session", gdb.COMMAND_USER)

    def invoke (self, arg, from_tty):
        global my_debugging_session
        # Variable: Symbol.is_argument
        arguments = [symbol for symbol in gdb.selected_frame().block() if symbol.is_argument]
        my_node = Node(gdb.selected_frame(), arguments)
        position = add_node_to_list(my_debugging_session.children, my_node, [])
        my_finish_br = MyFinishBreakpoint(position)
        my_finish_breakpoint = [breakpoint for breakpoint in gdb.breakpoints () if breakpoint.number == my_finish_br.number][0]
        my_br = gdb.Breakpoint(my_finish_breakpoint.location, temporary=False)
        my_br.commands = ("save-returning-node\n"
                          "c\n")
        my_finish_breakpoint.delete()

CommandAddNodeToSession()

def add_node_to_list(nodes, node, position):
    if nodes == [] or not nodes[-1].frame.is_valid() or nodes[-1].frame not in get_parent_frames(node):
        position.append(len(nodes))
        nodes.append(node)
        return position
    else:
        position.append(len(nodes)-1)
        return add_node_to_list(nodes[-1].children, node, position)

def get_parent_frames(node):
    parents = []
    aux_frame = node.frame.older()
    while aux_frame is not None:
        parents.append(aux_frame)
        aux_frame = aux_frame.older()
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
    for node in my_debugging_session.children:
        print(node.get_tree())

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

class MyFinishBreakpoint (gdb.FinishBreakpoint):
    def __init__(self, position):
        super(MyFinishBreakpoint, self).__init__()
        self.position = position
        self.commands = ("p \"joooder\"\n"
                         "reverse-step\n"
                         "save-returning-node\n"
                         "next"
                         "c")
        #self.associated_frame = frame
    def stop (self):
        global my_debugging_session
        get_node_from_position(my_debugging_session.children, self.position).return_value = self.return_value
        return True
    def out_of_scope(self):
        print("abnormal finish")

def get_node_from_position(nodes, position):
    if len(position) == 1:
        return nodes[position[0]]
    else:
        return get_node_from_position(nodes[position[0]].children, position[1:])

def get_node_from_frame(nodes, frame):
    for node in nodes:
        if node.frame == frame:
            return node
    return get_node_from_frame(nodes[-1].children, frame)

def get_last_node(nodes):
    if nodes == []:
        return None
    else:
        if nodes[-1].children == []:
            return nodes[-1]
        else:
            return get_last_node(nodes[-1].children)

def main():
    gdb.execute("del")
    gdb.execute("set pagination off")
    #gdb.execute("suspect-function quickSort(int*, int, int)")
    gdb.execute("suspect-function quickSort(int*, int, int, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >)")
    gdb.execute("suspect-function swap(int*, int*)")
    gdb.execute("suspect-function partition(int*, int, int)")
    gdb.execute("final-point print_array<int, 6ul>(int const (&) [6ul])")
    gdb.execute("start")
    gdb.execute("c")
    gdb.execute("c")

my_debugging_session = DebuggingSession()

main()
