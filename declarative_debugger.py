import gdb
from enum import Enum
from rich.tree import Tree
from rich import print
from simple_term_menu import TerminalMenu

class DebuggingSession:
    def __init__(self):
        self.node = None
        self.started = False
        self.finished = False

    def start(self):
        self.started = True

    def finish(self):
        self.finished = True

class Node:
    def __init__(self, frame, arguments=[], global_variables=[], object_state=None):
        self.frame = frame
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

    def get_tree(self, get_children=True, get_weight=True):
        tree = Tree(self.name)
        correct_tree = Tree("correctness")
        correct_tree.add(str(self.iscorrect))
        tree.add(correct_tree)
        if get_weight:
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
            my_debugging_session.node, gdb.newest_frame())
        my_node.finish(arguments=arguments)
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
        if (my_debugging_session.node == None):
            # First node
            my_debugging_session.node = my_node
            position = []
        else:
            position = add_node_to_tree(my_debugging_session.node, my_node, [])
        update_nodes_weight(my_debugging_session.node, position, 1)
        my_finish_br = MyFinishBreakpoint(position)
        my_finish_breakpoint = [breakpoint
                                for breakpoint in gdb.breakpoints()
                                if breakpoint.number == my_finish_br.number][0]
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
        options = ["Top-down", "Divide and Query (Hirunkitti)"]
        terminal_menu = TerminalMenu(options)
        menu_entry_index = terminal_menu.show()
        strategies_dict = {
            "Top-down": top_down_strategy,
            "Divide and Query (Hirunkitti)": divide_and_query_Hirunkitti_strategy
        }
        print(f"You have selected {options[menu_entry_index]}!")
        marked_execution_tree = my_debugging_session.node
        answer = ask_about_node(marked_execution_tree)
        if answer in [Answer.YES, Answer.TRUSTED]:
            print("No buggy node found")
            return
        elif answer is Answer.IDK:
            print("If you don't know, I cannot help you")
            return
        marked_execution_tree.evaluate_answer(Answer.NO)
        strategy = strategies_dict[options[menu_entry_index]]
        buggy_node = general_debugging_algorithm(marked_execution_tree, strategy)
        if buggy_node == None:
            print("No buggy node found")
            return
        print("Buggy node found")
        print(buggy_node.get_tree())

StartDeclarativeDebuggingSession()

class PrintNodes(gdb.Command):
    """Print nodes of declarative debugging session"""

    def __init__(self):
        super(PrintNodes, self).__init__("print-nodes", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        global my_debugging_session
        print(my_debugging_session.node.get_tree())

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
        get_node_from_position(my_debugging_session.node,
                               self.position).return_value = self.return_value
        return True

my_debugging_session = DebuggingSession()

# Functions

def general_debugging_algorithm(marked_execution_tree, strategy):
    while (marked_execution_tree is not None
           and not (marked_execution_tree.iscorrect == Answer.NO
                    and len(marked_execution_tree.children) == 0)):
        assert(marked_execution_tree.iscorrect == Answer.NO)
        selected_node, found, position = select_node(marked_execution_tree, strategy)
        assert(found)
        assert(selected_node.weight > 0)
        answer = ask_about_node(selected_node)
        selected_node.iscorrect = answer
        name = selected_node.name
        node_tree = selected_node.get_tree(get_weight=False)
        if (answer == Answer.NO):
            marked_execution_tree = selected_node
        elif answer in [Answer.YES, Answer.IDK, Answer.TRUSTED]:
            # Remove the node and remove the weight from all its parents
            update_nodes_weight(marked_execution_tree, position,
                                - get_node_from_position(marked_execution_tree, position).weight)
            remove_node_from_tree(marked_execution_tree, position)
        if (answer == Answer.YES):
            # Remove nodes with the same node_tree and remove the weight from all its parents
            found = True
            while (True):
                _, found, position = find_node_with_node_tree(marked_execution_tree, [], node_tree)
                if found == False:
                    break
                update_nodes_weight(marked_execution_tree, position,
                                    - get_node_from_position(marked_execution_tree, position).weight)
                deleted_tree = remove_node_from_tree(marked_execution_tree, position)
                if deleted_tree:
                    marked_execution_tree = None
                    break
        elif (answer == Answer.TRUSTED):
            # Remove nodes with the same name and remove the weight from all its parents
            found = True
            while (True):
                _, found, position = find_node_with_name(marked_execution_tree, [], name)
                if found is False:
                    break
                update_nodes_weight(marked_execution_tree, position,
                                    - get_node_from_position(marked_execution_tree, position).weight)
                deleted_tree = remove_node_from_tree(marked_execution_tree, position)
                if deleted_tree:
                    marked_execution_tree = None
                    break
    return marked_execution_tree

def select_node(marked_execution_tree, strategy):
    return strategy(marked_execution_tree, [])

def update_nodes_weight(marked_execution_tree, position, weight_delta):
    node_and_parents_positions = [position[:len(position)-n] for n in range(len(position))]
    node_and_parents_positions.append([])
    for node_position in node_and_parents_positions:
        get_node_from_position(marked_execution_tree,
                               node_position).weight += weight_delta

def add_node_to_tree(marked_execution_tree, node, position):
    if (len(marked_execution_tree.children) == 0
        or not marked_execution_tree.children[-1].frame.is_valid() # Or last child has finished
        or marked_execution_tree.children[-1].frame not in get_parent_frames(node)):
        marked_execution_tree.children.append(node)
        position.append(len(marked_execution_tree.children)-1)
        return position
    else:
        position.append(len(marked_execution_tree.children)-1)
        return add_node_to_tree(marked_execution_tree.children[-1], node, position)

def get_parent_frames(node):
    parents = []
    aux_frame = node.frame.older()
    while aux_frame is not None:
        parents.append(aux_frame)
        aux_frame = aux_frame.older()
    return parents


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

def discard_trusted_nodes(trusted_node, marked_execution_tree):
    gen = (node for node in marked_execution_tree if node.iscorrect == Answer.IDK)
    for node in gen:
        if node.name == trusted_node.name:
            node.iscorrect = Answer.TRUSTED
        discard_trusted_nodes(trusted_node, node.children)

def discard_correct_nodes(correct_node, nodes):
    gen = (node for node in nodes if node.iscorrect == Answer.IDK)
    for node in gen:
        if node.frame == correct_node.frame:
            node.iscorrect = Answer.YES
        discard_correct_nodes(correct_node, node.children)

def top_down_strategy(marked_execution_tree, position):
    """Search for closest undefined node.
    Returns:
    Found: bool
    Node
    Position: list of int
    """
    if (marked_execution_tree.iscorrect == Answer.IDK):
        return marked_execution_tree, True, position
    else:
        for index, child in enumerate(marked_execution_tree.children):
            tmp_marked_execution_tree, found, tmp_position = top_down_strategy(child, position)
            if found:
                tmp_position.append(index)
                return tmp_marked_execution_tree, found, tmp_position
    return None, False, []

def find_node_with_node_tree(marked_execution_tree, position, node_tree):
    """Search for closest node with frame.
    Returns:
    Found: bool
    Node
    Position: list of int
    """
    if (marked_execution_tree.get_tree(get_weight=False) == node_tree):
        return marked_execution_tree, True, position
    else:
        for index, child in enumerate(marked_execution_tree.children):
            tmp_marked_execution_tree, found, tmp_position = find_node_with_node_tree(child, position, node_tree)
            if found:
                tmp_position.insert(0, index)
                return tmp_marked_execution_tree, found, tmp_position
    return None, False, []

def find_node_with_name(marked_execution_tree, position, name):
    """Search for closest node with name.
    Returns:
    Found: bool
    Node
    Position: list of int
    """
    if (marked_execution_tree.name == name):
        return marked_execution_tree, True, position
    else:
        for index, child in enumerate(marked_execution_tree.children):
            tmp_marked_execution_tree, found, tmp_position = find_node_with_name(child, position, name)
            if found:
                tmp_position.insert(0, index)
                return tmp_marked_execution_tree, found, tmp_position
    return None, False, []

def divide_and_query_Hirunkitti_strategy(marked_execution_tree, position):
    # We select the child node whose weight is the closest to w(n)/2
    # w(child node) being >= w(n)/2
    # or w(child node) being <= w(n)/2
    assert(len(marked_execution_tree.children) > 0)
    pivot = marked_execution_tree.weight/2
    distance = marked_execution_tree.weight/2
    choosen_node = marked_execution_tree
    position = []
    for index, child in enumerate(marked_execution_tree.children):
        if abs(child.weight - pivot) < distance:
            distance = abs(child.weight - pivot)
            choosen_node = child
            position = [index]
    return choosen_node, True, position

def ask_about_node(node):
    print("Is the following node correct?")
    print(node.get_tree(get_children=False))
    options = ["Yes", "No", "I don't know", "Trusted"]
    terminal_menu = TerminalMenu(options)
    menu_entry_index = terminal_menu.show()
    answers_dict = {
        "Yes": Answer.YES,
        "No": Answer.NO,
        "I don't know": Answer.IDK,
        "Trusted": Answer.TRUSTED
    }
    return answers_dict[options[menu_entry_index]]

def get_node_from_position(marked_execution_tree, position):
    if len(position) == 0:
        return marked_execution_tree
    return get_node_from_position(marked_execution_tree.children[position[0]], position[1:])

def remove_node_from_tree(marked_execution_tree, position):
    """Returns true if marked_execution_tree should be deleted"""
    if len(position) == 0:
        return True
    elif len(position) == 1:
        marked_execution_tree.children.pop(position[0])
        return False
    else:
        return remove_node_from_tree(marked_execution_tree.children[position[0]], position[1:])

def get_node_from_frame(marked_execution_tree, frame):
    if marked_execution_tree.frame == frame and marked_execution_tree.arguments_when_returning == []:
        return marked_execution_tree
    return get_node_from_frame(marked_execution_tree.children[-1], frame)

def print_tree(node):
    print(node.get_tree())
