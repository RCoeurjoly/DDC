from enum import Enum
import gdb
from functions import *
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

class Node:
    def __init__(self, frame, arguments=[], global_variables=[], object_state=None):
        self.frame = frame
        # self.frame_hash = hash(frame)
        self.name = frame.name()
        self.weight = 0
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
                    array_indexes=True,
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
        self.iscorrect = Answer.IDK

    def get_tree(self, get_children=True):
        tree = Tree(self.name)
        correct_tree = Tree("correctness")
        correct_tree.add(str(self.iscorrect))
        tree.add(correct_tree)
        weight_tree = Tree("weight")
        weight_tree.add(str(self.weight))
        tree.add(weight_tree)
        if self.arguments_on_entry_tree != self.arguments_when_returning_tree:
            tree.add(self.arguments_on_entry_tree)
            tree.add(self.arguments_when_returning_tree)
        if get_children and len(self.children) > 0:
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
                    array_indexes=True,
                    symbols=True,
                    deref_refs=True))
            args_tree.add(arg_tree_name)
        self.arguments_when_returning_tree = args_tree
        self.global_variables_when_returning = global_variables
        self.object_state_when_returning = object_state
        self.return_value = return_value

    def evaluate(self, answer):
        if type(answer) is str:
            self.evaluate_str(answer)
        if type(answer) is Answer:
            self.evaluate_answer(answer)

    def evaluate_str(self, answer):
        if answer == "Yes":
            self.iscorrect = Answer.YES
        if answer == "No":
            self.iscorrect = Answer.NO
        if answer == "I don't know":
            self.iscorrect = Answer.IDK
        if answer == "Trusted":
            self.iscorrect = Answer.TRUSTED

    def evaluate_answer(self, answer):
        self.iscorrect = answer

class CommandFinishSession(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandFinishSession, self).__init__(
            "finish-debugging-session", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        global my_debugging_session
        my_debugging_session.finish()

CommandFinishSession()

class SetBreak(gdb.Breakpoint):
    def __init__(self, function, final=False):
        gdb.Breakpoint.__init__(self, function)
        self.final = final
        if final:
            self.commands = "finish-debugging-session"
        else:
            self.commands = ("add-node-to-session\n")
            # "c")
        self.silent = False

    def stop(self):
        return True  # stop the execution at this point

class SaveReturningNode(gdb.Command):
    """Save the info at the moment a node is returning in declarative debugging session"""

    def __init__(self):
        super(SaveReturningNode, self).__init__(
            "save-returning-node", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        gdb.execute("reverse-step")
        global my_debugging_session
        arguments = [symbol for symbol in gdb.newest_frame().block()
                     if symbol.is_argument]
        my_node = get_node_from_frame(
            my_debugging_session.children, gdb.newest_frame())
        my_node.finish(arguments=arguments)
        #my_node.arguments_when_returning = [1, 2]
        gdb.execute("n")
        return

SaveReturningNode()

class CommandAddNodeToSession(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandAddNodeToSession, self).__init__(
            "add-node-to-session", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        global my_debugging_session
        # Variable: Symbol.is_argument
        arguments = [symbol for symbol in gdb.selected_frame().block()
                     if symbol.is_argument]
        my_node = Node(gdb.selected_frame(), arguments)
        position = add_node_to_list(my_debugging_session.children, my_node, [])
        update_nodes_weight(my_debugging_session.children, position)
        my_finish_br = MyFinishBreakpoint(position)
        my_finish_breakpoint = [breakpoint for breakpoint in gdb.breakpoints(
        ) if breakpoint.number == my_finish_br.number][0]
        my_br = gdb.Breakpoint(my_finish_breakpoint.location, temporary=False)
        my_br.commands = ("save-returning-node\n")
        #    "c\n")
        my_finish_breakpoint.delete()

CommandAddNodeToSession()

class CommandSuspectFunction(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandSuspectFunction, self).__init__(
            "suspect-function", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        SetBreak(arg, False)

CommandSuspectFunction()

class CommandFinalBreakpoint(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandFinalBreakpoint, self).__init__(
            "final-point", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        SetBreak(arg, True)

CommandFinalBreakpoint()

class StartDeclarativeDebuggingSession(gdb.Command):
    """Set breakpoint on setField from Quickfix. It takes the tag number as argument"""

    def __init__(self):
        super(StartDeclarativeDebuggingSession, self).__init__(
            "start-declarative-debugging-session", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        global my_debugging_session
        my_finish_breakpoint = [breakpoint for breakpoint in gdb.breakpoints(
        ) if breakpoint.commands == "finish-debugging-session\n"]
        if len(my_finish_breakpoint) != 0:
            print(my_finish_breakpoint)
            hit_count = my_finish_breakpoint[0].hit_count
        else:
            hit_count = 0
        while (hit_count == 0 and gdb.selected_inferior().pid != 0):
            gdb.execute("c")
            if len(my_finish_breakpoint) != 0:
                hit_count = my_finish_breakpoint[0].hit_count
            else:
                hit_count = 0
        print("Finished building debugging tree. Please choose debugging strategy")
        options = ["Top-down", "Divide and Query (Shapiro)"]
        terminal_menu = TerminalMenu(options)
        menu_entry_index = terminal_menu.show()
        stategies_dict = {
            "Top-down": top_down_strategy,
            "Divide and Query (Shapiro)": divide_and_query_shapiro_strategy
        }
        print(f"You have selected {options[menu_entry_index]}!")
        marked_execution_tree = my_debugging_session.children[0]
        strategy = stategies_dict[options[menu_entry_index]]
        buggy_node = general_debugging_algorithm(marked_execution_tree, strategy)
        if buggy_node is not None:
            print("Buggy node found")
            print(buggy_node.get_tree())
        else:
            print("No buggy node found")

StartDeclarativeDebuggingSession()

class PrintNodes(gdb.Command):
    """Print nodes of declarative debugging session"""

    def __init__(self):
        super(PrintNodes, self).__init__("print-nodes", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        global my_debugging_session
        for node in my_debugging_session.children:
            print(node.get_tree())

PrintNodes()

class MyFinishBreakpoint (gdb.FinishBreakpoint):
    def __init__(self, position):
        super(MyFinishBreakpoint, self).__init__()
        self.position = position
        self.commands = ("reverse-step\n"
                         "save-returning-node\n"
                         "next")
        # "c")
        #self.associated_frame = frame

    def stop(self):
        global my_debugging_session
        get_node_from_position(my_debugging_session.children,
                               self.position).return_value = self.return_value
        return True

my_debugging_session = DebuggingSession()
