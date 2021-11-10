import gdb
from enum import Enum
from rich.tree import Tree
from rich import print
from simple_term_menu import TerminalMenu

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
        args_tree = Tree("args on entry")
        for arg in self.arguments_on_entry:
            arg_tree_name = arg.print_name + " = "
            if arg.print_name == "arr":
                arg_tree_name += str(gdb.parse_and_eval("*arr@6"))
            elif arg.value(self.frame).type.code == gdb.TYPE_CODE_PTR:
                arg_tree_name += str(arg.value(self.frame).dereference())
            else:
                arg_tree_name += str(arg.value(self.frame).format_string(
                    raw=False,
                    pretty_arrays=True,
                    pretty_structs=True,
                    array_indexes = True,
                    symbols=True,
                    deref_refs=True))
            args_tree.add(arg_tree_name)
        self.arguments_on_entry_tree = args_tree
        self.arguments_when_returning = []
        self.arguments_when_returning_tree = ""
        self.global_variables_on_entry = global_variables
        self.global_variables_when_returning = []
        self.object_state_on_entry = object_state
        self.object_state_when_returning = None
        self.return_value = None
        self.children = []
        self.correct = Answer.IDK

    def get_tree(self, get_children=True):
        tree = Tree(self.name)
        correct_tree = Tree("correctness")
        correct_tree.add(str(self.correct))
        tree.add(correct_tree)
        if self.arguments_on_entry_tree != self.arguments_when_returning_tree:
            tree.add(self.arguments_on_entry_tree)
            tree.add(self.arguments_when_returning_tree)
        if get_children:
            children_tree = Tree("children")
            # tree.add("children")
            for child in self.children:
                children_tree.add(child.get_tree())
            tree.add(children_tree)
        return tree

    def finish(self, arguments=None, global_variables=None, object_state=None, return_value=None):
        self.arguments_when_returning = arguments
        args = ""
        args_tree = Tree("args when returning")
        for arg in self.arguments_when_returning:
            arg_tree_name = arg.print_name + " = "
            if arg.print_name == "arr":
                arg_tree_name += str(gdb.parse_and_eval("*arr@6"))
            elif arg.value(self.frame).type.code == gdb.TYPE_CODE_PTR:
                arg_tree_name += str(arg.value(self.frame).dereference())
            else:
                arg_tree_name += str(arg.value(self.frame).format_string(
                    raw=False,
                    pretty_arrays=True,
                    pretty_structs=True,
                    array_indexes = True,
                    symbols=True,
                    deref_refs=True))
            args_tree.add(arg_tree_name)
        self.arguments_when_returning_tree = args_tree
        self.global_variables_when_returning = global_variables
        self.object_state_when_returning = object_state
        self.return_value = return_value

    def adopt(self, children_node):
        self.children.append(children_node)
    def evaluate(self, answer):
        if type(answer) is str:
            self.evaluate_str(answer)
        if type(answer) is Answer:
            self.evaluate_answer(answer)
    def evaluate_str(self, answer):
        if answer == "Yes":
            self.correct = Answer.YES
        if answer == "No":
            self.correct = Answer.NO
        if answer == "I don't know":
            self.correct = Answer.IDK
        if answer == "Trusted":
            self.correct = Answer.TRUSTED
    def evaluate_answer(self, answer):
        self.correct = answer
class SetBreak(gdb.Breakpoint):
    def __init__(self, function, final=False):
        gdb.Breakpoint.__init__(self, function)
        self.final = final
        if (final):
            self.commands = "finish-debugging-session"
        else:
            self.commands = ("add-node-to-session\n")
                             # "c")
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
        my_br.commands = ("save-returning-node\n")
                      #    "c\n")
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

class StartDeclarativeDebuggingSession(gdb.Command):
  """Set breakpoint on setField from Quickfix. It takes the tag number as argument"""

  def __init__ (self):
    super (StartDeclarativeDebuggingSession, self).__init__ ("start-declarative-debugging-session", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
    my_finish_breakpoint = [breakpoint for breakpoint in gdb.breakpoints() if breakpoint.commands == "finish-debugging-session\n"]
    if len(my_finish_breakpoint) is not 0:
        print(my_finish_breakpoint)
        hit_count = my_finish_breakpoint[0].hit_count
    else:
        hit_count = 0
    while (hit_count == 0 and gdb.selected_inferior().pid is not 0):
        gdb.execute("c")
        if len(my_finish_breakpoint) is not 0:
            hit_count = my_finish_breakpoint[0].hit_count
        else:
            hit_count = 0
    print("Finished building debugging tree. Please choose debugging strategy")
    options = ["Top-down", "Divide and query"]
    terminal_menu = TerminalMenu(options)
    menu_entry_index = terminal_menu.show()
    print(f"You have selected {options[menu_entry_index]}!")
    for node in my_debugging_session.children:
        buggy_node = top_down_strategy(node)
        print("Buggy node found")
        print(buggy_node.get_tree(False))

StartDeclarativeDebuggingSession()

class PrintNodes(gdb.Command):
  """Print nodes of declarative debugging session"""

  def __init__ (self):
    super (PrintNodes, self).__init__ ("print-nodes", gdb.COMMAND_USER)

  def invoke (self, arg, from_tty):
    for node in my_debugging_session.children:
        print(node.get_tree())

PrintNodes()

class Answer(Enum):
    YES = 1
    NO = 2
    IDK = 3
    TRUSTED = 4
    def describe(self):
        # self is the member here
        return self.name, self.value
    def __str__(self):
        if self.value == 1:
            return "yes"
        if self.value == 2:
            return "no"
        if self.value == 3:
            return "I don't know"
        if self.value == 4:
            return "trusted"

def discard_trusted_nodes(trusted_node, nodes):
    gen = (node for node in nodes if node.correct == Answer.IDK)
    for node in gen:
        if node.name == trusted_node.name:
            print("Trusting node!")
            node.correct = Answer.TRUSTED
            print(str(node.correct))
            print(node.get_tree(False))
        discard_trusted_nodes(trusted_node, node.children)

def discard_correct_nodes(correct_node, nodes):
    gen = (node for node in nodes if node.correct == Answer.IDK)
    for node in gen:
        if node.frame == correct_node.frame:
            print("Correcting node!")
            node.correct = Answer.YES
            print(node.get_tree(False))
        discard_correct_nodes(correct_node, node.children)

def top_down_strategy(node):
    children_nodes_are_valid = True
    invalid_child = None
    gen = (child_node for child_node in node.children if child_node.correct == Answer.IDK)
    for child_node in gen:
        ask_about_node(child_node)
        if child_node.correct == Answer.YES:
            discard_correct_nodes(child_node, my_debugging_session.children)
        if child_node.correct == Answer.TRUSTED:
            discard_trusted_nodes(child_node, my_debugging_session.children)
        if child_node.correct == Answer.NO:
            children_nodes_are_valid = False
            invalid_child = child_node
            break
    if children_nodes_are_valid:
        return node
    else:
        return top_down_strategy(invalid_child)

def ask_about_node(node):
    print("Is the following node correct?")
    print(node.get_tree(False))
    options = ["Yes", "No", "I don't know", "Trusted"]
    terminal_menu = TerminalMenu(options)
    menu_entry_index = terminal_menu.show()
    node.evaluate(options[menu_entry_index])

class MyFinishBreakpoint (gdb.FinishBreakpoint):
    def __init__(self, position):
        super(MyFinishBreakpoint, self).__init__()
        self.position = position
        self.commands = ("reverse-step\n"
                         "save-returning-node\n"
                         "next")
                        # "c")
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
        if node.frame == frame and node.arguments_when_returning == []:
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
    # gdb.execute("start-declarative-debugging-session")


my_debugging_session = DebuggingSession()

main()
