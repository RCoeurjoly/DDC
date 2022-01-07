import json
import socket
import pickle
from enum import Enum
from functools import reduce
from typing import Union, List, Callable, Optional, Tuple
import gdb # type: ignore
from rich.tree import Tree
from rich import print as print_tree
from simple_term_menu import TerminalMenu # type: ignore

# Constants

HOST = 'localhost'
PORT = 50007

# Classes

class ComparableTree(Tree):
    def __eq__(self, other: object) -> bool:
        return (isinstance(other, self.__class__)
            and self.to_json() == other.to_json())

    def to_json(self):
        return json.dumps(self, default=lambda o: o.__dict__,
            sort_keys=True, indent=4)

class DebuggingSession:
    def __init__(self) -> None:
        self.node = None
        self.started = False
        self.is_tree_built = False

    def start(self) -> None:
        self.started = True

    def tree_built(self) -> None:
        self.is_tree_built = True

class Node:
    def __init__(self,
                 function_name: str,
                 frame: Optional[gdb.Frame] = None,
                 arguments: Optional[List[gdb.Symbol]] = None,
                 global_variables: Optional[List[gdb.Symbol]] = None,
                 object_state: Optional[gdb.Symbol] = None,
                 position: List[int] = []) -> None:
        self.frame = frame
        self.function_name = function_name
        self.weight = 0
        self.arguments_on_entry = arguments
        self.arguments_on_entry_tree: Optional[ComparableTree] = None
        if self.arguments_on_entry:
            args_tree = ComparableTree("args on entry")
            self.arguments_on_entry_tree = get_tree_from_arguments(args_tree,
                                                                   arguments,
                                                                   self.frame)
        self.arguments_when_returning: List[gdb.Symbol] = []
        self.arguments_when_returning_tree: Optional[ComparableTree] = None
        self.global_variables_on_entry = global_variables
        self.global_variables_when_returning: Optional[List[gdb.Symbol]] = []
        self.object_state_on_entry = object_state
        self.object_state_when_returning = None
        self.return_value: Optional[gdb.Value] = None
        self.return_value_tree: Optional[ComparableTree] = None
        self.children: List[Node] = []
        self.iscorrect: Correctness = Correctness.IDK
        self.finished: bool = False
        self.position: List[int] = position
        self.saving_br_number: int = 0

    def deepcopy(self, node):
        self.frame = None
        self.function_name = node.function_name
        self.weight = node.weight
        self.arguments_on_entry = node.arguments_on_entry
        self.arguments_on_entry_tree = node.arguments_on_entry_tree
        self.arguments_when_returning = node.arguments_when_returning
        self.arguments_when_returning_tree = node.arguments_when_returning_tree
        self.global_variables_on_entry = node.global_variables_on_entry
        self.global_variables_when_returning = node.global_variables_when_returning
        self.object_state_on_entry = node.object_state_on_entry
        self.object_state_when_returning = node.object_state_when_returning
        self.return_value = node.return_value
        self.children = []
        for child in node.children:
            temp = Node("temp")
            temp.deepcopy(child)
            self.children.append(temp)
        self.iscorrect = node.iscorrect

    def get_tree(self,
                 get_children: bool = True,
                 get_weight: bool = True,
                 get_correctness: bool = True) -> ComparableTree:
        tree = ComparableTree(self.function_name)
        if get_correctness:
            correct_tree = ComparableTree("correctness")
            correct_tree.add(str(self.iscorrect))
            tree.add(correct_tree)
        if get_weight:
            weight_tree = ComparableTree("weight")
            weight_tree.add(str(self.weight))
            tree.add(weight_tree)
        if self.arguments_on_entry_tree is not None:
            tree.add(self.arguments_on_entry_tree)
        else:
            # assert False
            pass
        if self.arguments_when_returning_tree is not None:
            tree.add(self.arguments_when_returning_tree)
        else:
            # assert False
            pass
        if self.return_value_tree:
            tree.add(self.return_value_tree)
        elif self.return_value is not None:
            return_value_tree = ComparableTree("return value")
            return_value_tree.add(self.return_value.format_string())
            self.return_value_tree = return_value_tree
            tree.add(self.return_value_tree)
        if get_children and len(self.children) > 0:
            children_tree = ComparableTree("children")
            for child in self.children:
                children_tree.add(child.get_tree())
            tree.add(children_tree)
        return tree

    def finish(self,
               arguments: Optional[List[gdb.Symbol]] = None,
               global_variables: Optional[List[gdb.Symbol]] = None,
               object_state: Optional[gdb.Symbol] = None) -> None:
        assert self.frame.is_valid()
        pointer_or_ref_args = get_pointer_or_ref(arguments, self.frame)
        if arguments and len(arguments) > 0 and len(pointer_or_ref_args) > 0:
            self.arguments_when_returning = arguments
            args_tree = ComparableTree("args when returning")
            self.arguments_when_returning_tree = get_tree_from_arguments(args_tree,
                                                                         pointer_or_ref_args,
                                                                         self.frame)
        else:
            assert False
        self.global_variables_when_returning = global_variables
        self.object_state_when_returning = object_state
        self.finished = True

    def evaluate_answer(self, answer):
        self.iscorrect = answer

# Global variables

MY_DEBUGGING_SESSION = DebuggingSession()
CORRECT_NODE_TREES: List[ComparableTree] = []
PENDING_CORRECT_NODES: List[Node] = []

# GDB Commands

class CommandFinishSession(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandFinishSession, self).__init__(
            "finish-debugging-session", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        global MY_DEBUGGING_SESSION
        MY_DEBUGGING_SESSION.tree_built()

CommandFinishSession()

class SaveReturningNode(gdb.Command):
    """Save the info at the moment a node is returning in declarative debugging session"""

    def __init__(self):
        super(SaveReturningNode, self).__init__(
            "save-returning-node", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        gdb.execute("reverse-step") # To execute this command, rr is needed
        arguments = [symbol for symbol in gdb.newest_frame().block()
                     if symbol.is_argument]
        my_node = get_unfinished_node_from_frame(
            MY_DEBUGGING_SESSION.node, gdb.newest_frame())
        assert my_node.frame == gdb.newest_frame()
        my_node.finish(arguments=arguments)
        if my_node.get_tree(False, False, False) in CORRECT_NODE_TREES:
            update_nodes_weight(MY_DEBUGGING_SESSION.node, my_node.position, -1)
            remove_node_from_tree(MY_DEBUGGING_SESSION.node, my_node.position)
        gdb.execute("n")

SaveReturningNode()

class SaveReturningCorrectNode(gdb.Command):
    """Save the info at the moment a node is returning in correct nodes list"""

    def __init__(self):
        super(SaveReturningCorrectNode, self).__init__(
            "save-returning-correct-node", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        gdb.execute("reverse-step") # To execute this command, rr is needed
        assert len(PENDING_CORRECT_NODES) > 0
        arguments = [symbol for symbol in gdb.newest_frame().block()
                     if symbol.is_argument]
        for pending_correct_node in PENDING_CORRECT_NODES:
            assert pending_correct_node.finished is False
            assert pending_correct_node.frame.is_valid()
        my_node = PENDING_CORRECT_NODES[-1]
        assert my_node.frame == gdb.newest_frame()
        my_node.finish(arguments=arguments)
        assert my_node.finished
        my_node_tree = my_node.get_tree(get_children=False, get_weight=False, get_correctness=False)
        CORRECT_NODE_TREES.append(my_node_tree)
        assert len(CORRECT_NODE_TREES) > 0
        PENDING_CORRECT_NODES.pop()
        gdb.execute("n")

SaveReturningCorrectNode()

class CommandAddNodeToSession(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandAddNodeToSession, self).__init__(
            "add-node-to-session", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        # Variable: Symbol.is_argument
        global MY_DEBUGGING_SESSION
        arguments = [symbol for symbol in gdb.selected_frame().block() if symbol.is_argument]
        function_name = arg
        my_node = Node(function_name, gdb.selected_frame(), arguments)
        if MY_DEBUGGING_SESSION.node is None:
            # First node
            MY_DEBUGGING_SESSION.node = my_node
            position = []
        else:
            position = add_node_to_tree(MY_DEBUGGING_SESSION.node, my_node, [])
        my_node.position = position
        update_nodes_weight(MY_DEBUGGING_SESSION.node, position, 1)
        MyFinishBreakpoint(position)

CommandAddNodeToSession()

class CommandAddNodeToCorrectList(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandAddNodeToCorrectList, self).__init__(
            "add-node-to-correct-list", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        # Variable: Symbol.is_argument
        arguments = [symbol for symbol in gdb.selected_frame().block()
                     if symbol.is_argument]
        function_name = arg
        my_node = Node(function_name, gdb.selected_frame(), arguments)
        PENDING_CORRECT_NODES.append(my_node)
        position = len(PENDING_CORRECT_NODES) - 1
        MyReferenceFinishBreakpoint(position)

CommandAddNodeToCorrectList()

class CommandSuspectFunction(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandSuspectFunction, self).__init__(
            "suspect-function", gdb.COMMAND_USER, gdb.COMPLETE_LOCATION)

    def invoke(self, arg, from_tty):
        SetSuspectBreak(arg)

CommandSuspectFunction()

class CommandSaveCorrectFunction(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandSaveCorrectFunction, self).__init__(
            "save-correct-function", gdb.COMMAND_USER, gdb.COMPLETE_LOCATION)

    def invoke(self, arg, from_tty):
        SetReferenceBreak(arg)

CommandSaveCorrectFunction()

class CommandFinalBreakpoint(gdb.Command):
    """Set breakpoint for ending debugging session"""

    def __init__(self):
        super(CommandFinalBreakpoint, self).__init__(
            "final-point", gdb.COMMAND_USER, gdb.COMPLETE_LOCATION)

    def invoke(self, arg, from_tty):
        SetFinalBreak(arg)

CommandFinalBreakpoint()

class StartDeclarativeDebuggingSession(gdb.Command):
    """Set breakpoint on setField from Quickfix. It takes the tag number as argument"""

    def __init__(self):
        super(StartDeclarativeDebuggingSession, self).__init__(
            "start-declarative-debugging-session", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        if can_start_asking_questions():
            return ask_questions()
        if can_start_building_tree():
            print("Building tree")
            if build_tree():
                global MY_DEBUGGING_SESSION
                tree_transformations = [simplified_tree_compression]
                # tree_transformations = []
                for tree_transformation in tree_transformations:
                    apply_tree_transformations(MY_DEBUGGING_SESSION.node, tree_transformation)
                return ask_questions()
            return False
        return False

StartDeclarativeDebuggingSession()

class TilTheEnd(gdb.Command):
    """Set breakpoint on setField from Quickfix. It takes the tag number as argument"""

    def __init__(self):
        super(TilTheEnd, self).__init__(
            "til-the-end", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        initial_br_number = len([breakpoint for breakpoint in gdb.breakpoints()
                                 if breakpoint.commands.startswith("add-node-to-correct-list")])
        # Reaching first correct function, which is going to create a finish breakpoint
        total_br_number = len(gdb.breakpoints())
        while total_br_number == initial_br_number:
            gdb.execute("c")
            total_br_number = len(gdb.breakpoints())
        # The sum of hit_count of all correct nodes should be greater than 0
        assert reduce(lambda x, y: x + y,
                      [breakpoint.hit_count for breakpoint in gdb.breakpoints()
                       if breakpoint.commands.startswith("add-node-to-correct-list")]) > 0
        while gdb.selected_inferior().pid != 0:
            gdb.execute("c")
            total_br_number = len(gdb.breakpoints())

TilTheEnd()

class ListenForCorrectNodes(gdb.Command):

    def __init__(self):
        super(ListenForCorrectNodes, self).__init__(
            "listen-for-correct-nodes", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        my_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        my_socket.bind((HOST, PORT))
        my_socket.listen(1)
        gdb.execute("set pagination off")
        conn = None
        while True:
            try:
                conn, addr = my_socket.accept()
                print('Connected by', addr)
                data = conn.recv(4096)
                if not data:
                    continue
                CORRECT_NODE_TREES.append(pickle.loads(data))
            except KeyboardInterrupt:
                if conn:
                    conn.close()
                break

ListenForCorrectNodes()

class SendCorrectNodes(gdb.Command):

    def __init__(self):
        super(SendCorrectNodes, self).__init__(
            "send-correct-nodes", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        for index, correct_node_tree in enumerate(CORRECT_NODE_TREES):
            my_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            my_socket.connect((HOST, PORT))
            # Pickle the object and send it to the server
            data_string = pickle.dumps(correct_node_tree)
            print("Sending node n# " + str(index))
            my_socket.send(data_string)
        my_socket.close()

SendCorrectNodes()

class PrintTree(gdb.Command):
    """Print nodes of declarative debugging session"""

    def __init__(self):
        super(PrintTree, self).__init__(
            "print-tree", gdb.COMMAND_USER)

    def invoke(self, arg, from_tty):
        print_tree(MY_DEBUGGING_SESSION.node.get_tree())

PrintTree()

# Breakpoints


class SetFinalBreak(gdb.Breakpoint):
    def __init__(self, function):
        gdb.Breakpoint.__init__(self, function)
        self.commands = "finish-debugging-session\n"
        self.silent = True

    def stop(self):
        return True  # stop the execution at this point

class SetSuspectBreak(gdb.Breakpoint):
    def __init__(self, function):
        gdb.Breakpoint.__init__(self, function)
        self.commands = ("add-node-to-session " + function + "\n")
        self.silent = True

    def stop(self):
        return True  # do not stop the execution at this point

class SetReferenceBreak(gdb.Breakpoint):
    def __init__(self, function):
        gdb.Breakpoint.__init__(self, function)
        self.commands = ("add-node-to-correct-list " + function + "\n")
        self.silent = True

    def stop(self):
        return True  # stop the execution at this point

# Finish breakpoints

class MyFinishBreakpoint(gdb.FinishBreakpoint):
    def __init__(self, position):
        super(MyFinishBreakpoint, self).__init__()
        self.position = position
        self.commands = ("save-returning-node")
        self.silent = True

    def stop(self):
        global MY_DEBUGGING_SESSION
        my_node = get_node_from_position(MY_DEBUGGING_SESSION.node, self.position)
        my_node.return_value = self.return_value
        return True

class MyReferenceFinishBreakpoint(gdb.FinishBreakpoint):
    def __init__(self, position):
        super(MyReferenceFinishBreakpoint, self).__init__()
        self.position = position
        self.commands = ("save-returning-correct-node")
        self.silent = True

    def stop(self):
        global PENDING_CORRECT_NODES
        PENDING_CORRECT_NODES[self.position].return_value = self.return_value
        return True

# Functions

def general_debugging_algorithm(marked_execution_tree: Optional[Node],
                                strategy: Callable[[Node,
                                                    List[int]],
                                                   Tuple[Node, bool, List[int]]]) -> Optional[Node]:
    while (marked_execution_tree is not None
           and not (marked_execution_tree.iscorrect == Correctness.NO
                    and len(marked_execution_tree.children) == 0)):
        assert marked_execution_tree.iscorrect == Correctness.NO
        selected_node, found, position = select_node(marked_execution_tree, strategy)
        assert found
        assert selected_node.weight > 0
        answer = ask_about_node_with_extra_functionality(selected_node)
        if answer == ExtraFunctionality.CHANGE_STRATEGY:
            strategy = strategies_dict[choose_strategy()]
            continue
        selected_node.iscorrect = answer
        function_name = selected_node.function_name
        node_tree = selected_node.get_tree(get_children=False,
                                           get_weight=False,
                                           get_correctness=False)
        if answer == Correctness.NO:
            marked_execution_tree = selected_node
        elif answer in [Correctness.YES, Correctness.IDK, Correctness.TRUSTED]:
            # Remove the node and remove the weight from all its parents
            update_nodes_weight(marked_execution_tree, position,
                                - get_node_from_position(marked_execution_tree, position).weight)
            remove_node_from_tree(marked_execution_tree, position)
        if answer == Correctness.YES:
            # Remove nodes with the same node_tree and remove the weight from all its parents
            found = True
            while True:
                _, found, position = find_node_with_node_tree(marked_execution_tree, [], node_tree)
                if found is False:
                    break
                update_nodes_weight(marked_execution_tree,
                                    position,
                                    - get_node_from_position(marked_execution_tree,
                                                             position).weight)
                deleted_tree = remove_node_from_tree(marked_execution_tree, position)
                if deleted_tree:
                    marked_execution_tree = None
                    break
        elif answer == Correctness.TRUSTED:
            # Remove nodes with the same name and remove the weight from all its parents
            found = True
            while True:
                _, found, position = find_node_with_name(marked_execution_tree, [], function_name)
                if found is False:
                    break
                update_nodes_weight(marked_execution_tree,
                                    position,
                                    - get_node_from_position(marked_execution_tree,
                                                             position).weight)
                deleted_tree = remove_node_from_tree(marked_execution_tree, position)
                if deleted_tree:
                    marked_execution_tree = None
                    break
    return marked_execution_tree

def select_node(marked_execution_tree: Node,
                strategy: Callable[[Node, List[int]],
                                   Tuple[Node, bool, List[int]]]) -> Tuple[Node, bool, List[int]]:
    return strategy(marked_execution_tree, [])

def update_nodes_weight(marked_execution_tree: Node,
                        position: List[int],
                        weight_delta: int) -> None:
    node_and_parents_positions = [position[:len(position)-n] for n in range(len(position))]
    node_and_parents_positions.append([])
    for node_position in node_and_parents_positions:
        get_node_from_position(marked_execution_tree,
                               node_position).weight += weight_delta

def add_node_to_tree(marked_execution_tree: Node,
                     node: Node,
                     position: List[int]) -> List[int]:
    if (len(marked_execution_tree.children) == 0
        or not marked_execution_tree.children[-1].frame.is_valid() # Or last child has finished
        or marked_execution_tree.children[-1].frame not in get_parent_frames(node)):
        marked_execution_tree.children.append(node)
        position.append(len(marked_execution_tree.children)-1)
        return position
    position.append(len(marked_execution_tree.children)-1)
    return add_node_to_tree(marked_execution_tree.children[-1], node, position)

def get_parent_frames(node: Node) -> List[gdb.Frame]:
    parents = []
    aux_frame = node.frame.older()
    while aux_frame is not None:
        parents.append(aux_frame)
        aux_frame = aux_frame.older()
    return parents

class Correctness(Enum):
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
        return ""

class ExtraFunctionality(Enum):
    UNDO = 5
    CHANGE_STRATEGY = 6

def top_down_strategy(marked_execution_tree: Node,
                      position: List[int]) -> Tuple[Optional[Node], bool, List[int]]:
    """Search for closest undefined node.
    Returns:
    Found: bool
    Node
    Position: list of int
    """
    if marked_execution_tree.iscorrect == Correctness.IDK:
        return marked_execution_tree, True, position
    for index, child in enumerate(marked_execution_tree.children):
        tmp_marked_execution_tree, found, tmp_position = top_down_strategy(child, position)
        if found:
            tmp_position.append(index)
            return tmp_marked_execution_tree, found, tmp_position
    return None, False, []


def divide_and_query_hirunkitti_strategy(marked_execution_tree: Node,
                                         position: List[int]) -> Tuple[Node, bool, List[int]]:
    # We select the child node whose weight is the closest to w(n)/2
    # w(child node) being >= w(n)/2
    # or w(child node) being <= w(n)/2
    assert len(marked_execution_tree.children) > 0
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

def heaviest_first_strategy(marked_execution_tree: Node,
                            position: List[int]) -> Tuple[Node, bool, List[int]]:
    # We select the child node whose weight is the heaviest
    assert len(marked_execution_tree.children) > 0
    heaviest_weight = 0
    for index, child in enumerate(marked_execution_tree.children):
        if child.weight > heaviest_weight:
            heaviest_weight = child.weight
            choosen_node = child
            position = [index]
    return choosen_node, True, position

strategies_dict = {
    "Top-down": top_down_strategy,
    "Divide and Query (Hirunkitti)": divide_and_query_hirunkitti_strategy,
    "Heaviest first": heaviest_first_strategy
}

strategy_options = ["Top-down",
                    "Divide and Query (Hirunkitti)",
                    "Heaviest first"]

def find_node_with_node_tree(marked_execution_tree: Node,
                             position: List[int],
                             node_tree: ComparableTree) -> Tuple[Optional[Node], bool, List[int]]:
    """Search for closest node with frame.
    Returns:
    Found: bool
    Node
    Position: list of int
    """
    if (marked_execution_tree.get_tree(get_children=False,
                                       get_weight=False,
                                       get_correctness=False) == node_tree):
        return marked_execution_tree, True, position
    for index, child in enumerate(marked_execution_tree.children):
        tmp_marked_execution_tree, found, tmp_position = find_node_with_node_tree(child,
                                                                                  position,
                                                                                  node_tree)
        if found:
            tmp_position.insert(0, index)
            return tmp_marked_execution_tree, found, tmp_position
    return None, False, []

def find_node_with_name(marked_execution_tree: Node,
                        position: List[int],
                        function_name: str) -> Tuple[Optional[Node], bool, List[int]]:
    """Search for closest node with name.
    Returns:
    Found: bool
    Node
    Position: list of int
    """
    if marked_execution_tree.function_name == function_name:
        return marked_execution_tree, True, position
    for index, child in enumerate(marked_execution_tree.children):
        tmp_marked_execution_tree, found, tmp_position = find_node_with_name(child,
                                                                             position,
                                                                             function_name)
        if found:
            tmp_position.insert(0, index)
            return tmp_marked_execution_tree, found, tmp_position
    return None, False, []

def ask_about_node_with_extra_functionality(node: Node) -> Union[Correctness, ExtraFunctionality]:
    print("Is the following node correct?")
    print_tree(node.get_tree(get_children=False))
    correctness_options = ["Yes", "No", "I don't know", "Trusted"]
    total_options = correctness_options + [
        # "Undo",
        "Change strategy"]
    terminal_menu = TerminalMenu(total_options)
    menu_entry_index = terminal_menu.show()
    answers_dict = {
        "Yes": Correctness.YES,
        "No": Correctness.NO,
        "I don't know": Correctness.IDK,
        "Trusted": Correctness.TRUSTED,
        # "Undo": ExtraFunctionality.UNDO,
        "Change strategy": ExtraFunctionality.CHANGE_STRATEGY
    }
    return answers_dict[total_options[menu_entry_index]]

def ask_about_node(node: Node) -> Union[Correctness, ExtraFunctionality]:
    print("Is the following node correct?")
    print_tree(node.get_tree(get_children=False))
    correctness_options = ["Yes", "No", "I don't know", "Trusted"]
    terminal_menu = TerminalMenu(correctness_options)
    menu_entry_index = terminal_menu.show()
    answers_dict = {
        "Yes": Correctness.YES,
        "No": Correctness.NO,
        "I don't know": Correctness.IDK,
        "Trusted": Correctness.TRUSTED
    }
    return answers_dict[correctness_options[menu_entry_index]]

def get_node_from_position(marked_execution_tree: Node,
                           position: List[int]) -> Node:
    if len(position) == 0:
        return marked_execution_tree
    return get_node_from_position(marked_execution_tree.children[position[0]], position[1:])

def remove_node_from_tree(marked_execution_tree: Node,
                          position: List[int]) -> bool:
    """Returns true if marked_execution_tree should be deleted"""
    if len(position) == 0:
        return True
    if len(position) == 1:
        marked_execution_tree.children.pop(position[0])
        return False
    return remove_node_from_tree(marked_execution_tree.children[position[0]], position[1:])

def get_unfinished_node_from_frame(marked_execution_tree: Node,
                        frame: gdb.Frame) -> Node:
    # If the frame coincides, we also check that is an unfinished node
    if marked_execution_tree.frame == frame and marked_execution_tree.finished is False:
        return marked_execution_tree
    assert len(marked_execution_tree.children) > 0
    return get_unfinished_node_from_frame(marked_execution_tree.children[-1], frame)

def get_pointer_or_ref(arguments: Optional[List[gdb.Symbol]], frame: gdb.Frame) -> List[gdb.Symbol]:
    if arguments is None:
        return []
    return [argument for argument in arguments
            if argument.value(frame).type.code in [gdb.TYPE_CODE_PTR, gdb.TYPE_CODE_REF]]

def can_start_asking_questions() -> bool:
    if MY_DEBUGGING_SESSION.is_tree_built is True:
        return True
    return False

def get_suspect_plus_final_br_number():
    return len([breakpoint for breakpoint in gdb.breakpoints()
                if (breakpoint.commands == "finish-debugging-session\n"
                    or breakpoint.commands.startswith("add-node-to-session "))])

def can_start_building_tree() -> bool:
    """Returns true if:
    - there are suspect breakpoints
    - and if total br is equal to suspect and final br.
    False otherwise"""
    suspect_br_number = len([breakpoint for breakpoint in gdb.breakpoints()
                             if breakpoint.commands.startswith("add-node-to-session ")])
    suspect_plus_final_br_number = get_suspect_plus_final_br_number()
    total_br_number = len(gdb.breakpoints())
    if suspect_br_number > 0:
        if suspect_plus_final_br_number == total_br_number:
            return True
        print("Please delete all breakpoints that are not suspect or final")
        return False
    print("Please add suspect breakpoint(s)")
    return False

def build_tree() -> bool:
    """Returns True if tree was built successfully. False otherwise"""
    initial_br_number = get_suspect_plus_final_br_number()
    # Reaching first suspect function, which is going to create a finish breakpoint
    total_br_number = len(gdb.breakpoints())
    while total_br_number == initial_br_number:
        gdb.execute("c")
        total_br_number = len(gdb.breakpoints())
    # The sum of hit_count of all suspect nodes should be greater than 0
    assert reduce(lambda x, y: x + y,
                  [breakpoint.hit_count for breakpoint in gdb.breakpoints()
                   if breakpoint.commands.startswith("add-node-to-session ")]) > 0
    # First finish breakpoint reached, reaching final state
    # If a final-point has already been reached, exit with error
    is_hit, my_breakpoint = hit_final_breakpoint()
    if is_hit:
        print("Final breakpoint " + str(my_breakpoint.number)
              + " has been hit " + str(my_breakpoint.hit_count)
              + ". Please reconsider")
        return False
    while total_br_number != initial_br_number:
        gdb.execute("c")
        total_br_number = len(gdb.breakpoints())
    MY_DEBUGGING_SESSION.tree_built()
    return True

def hit_final_breakpoint():
    for my_breakpoint in [breakpoint for breakpoint in gdb.breakpoints()
                       if breakpoint.commands == "finish-debugging-session\n"]:
        if my_breakpoint.hit_count > 0:
            return True, my_breakpoint
    return False, None

def choose_strategy():
    print("Please choose debugging strategy")
    terminal_menu = TerminalMenu(strategy_options)
    menu_entry_index = terminal_menu.show()
    print(f"You have selected {strategy_options[menu_entry_index]}!")
    return strategy_options[menu_entry_index]

def ask_questions() -> bool:
    """Returns True if buggy node is found. False otherwise"""
    strategy = strategies_dict[choose_strategy()]
    assert MY_DEBUGGING_SESSION.is_tree_built
    marked_execution_tree = Node("frame")
    marked_execution_tree.deepcopy(MY_DEBUGGING_SESSION.node)
    answer = ask_about_node(marked_execution_tree)
    if answer in [Correctness.YES, Correctness.TRUSTED]:
        print("No buggy node found")
        assert False
        return False
    if answer is Correctness.IDK:
        print("If you don't know, I cannot help you")
        return False
    marked_execution_tree.evaluate_answer(Correctness.NO)
    buggy_node = general_debugging_algorithm(marked_execution_tree, strategy)
    if buggy_node is None:
        print("No buggy node found")
        return False
    print("Buggy node found")
    print_tree(buggy_node.get_tree())
    # assert False
    return True

def can_node_be_compressed(marked_execution_tree: Node) -> Tuple[bool, int]:
    """Searches for the longest compression possible. Returns:
    - bool: True if can be compressed. False otherwise
    - int: If it can be compressed, number of nodes to compress"""
    if len(marked_execution_tree.children) != 1:
        return False, 0
    if marked_execution_tree.children[0].function_name != marked_execution_tree.function_name:
        return False, 0
    _, downstream_length = can_node_be_compressed(marked_execution_tree.children[0])
    return True, downstream_length + 1

def compress_node(marked_execution_tree: Node, nodes_to_compress: int) -> Node:
    head_node = marked_execution_tree
    tail_node = marked_execution_tree
    for _ in range(nodes_to_compress):
        tail_node = tail_node.children[0]
    compressed_node = tail_node
    compressed_node.arguments_on_entry_tree = head_node.arguments_on_entry_tree
    compressed_node.return_value_tree = head_node.return_value_tree
    compressed_node.function_name = head_node.function_name + "^" + str(nodes_to_compress + 1)
    return compressed_node

def compress_node_in_position_and_update_weight(marked_execution_tree: Node,
                                                position: List[int],
                                                nodes_to_compress: int) -> None:
    get_node_from_position(
        marked_execution_tree,
        position).deepcopy(
            compress_node(
                get_node_from_position(marked_execution_tree,
                                       position), nodes_to_compress))
    update_nodes_weight(marked_execution_tree, position, - nodes_to_compress)
    get_node_from_position(marked_execution_tree, position).weight += nodes_to_compress

def simplified_tree_compression(marked_execution_tree: Node, position: List[int]) -> None:
    compress, nodes_to_compress = can_node_be_compressed(marked_execution_tree)
    if compress:
        compress_node_in_position_and_update_weight(marked_execution_tree,
                                                    position,
                                                    nodes_to_compress)
    for index, child_node in enumerate(marked_execution_tree.children):
        compress, nodes_to_compress = can_node_be_compressed(child_node)
        if compress:
            position.append(index)
            compress_node_in_position_and_update_weight(marked_execution_tree,
                                                        position,
                                                        nodes_to_compress)

def apply_tree_transformations(marked_execution_tree: Node, tree_transformation):
    tree_transformation(marked_execution_tree, [])

def get_tree_from_arguments(args_tree_root, arguments, frame):
    assert len(arguments) > 0
    assert frame.is_valid()
    args_tree = args_tree_root
    for arg in arguments:
        arg_tree_name = arg.print_name + " = "
        if arg.value(frame).type.code == gdb.TYPE_CODE_PTR:
            arg_tree_name += str(arg.value(frame).dereference())
        else:
            arg_tree_name += str(arg.value(frame).format_string(
                raw=False,
                pretty_arrays=True,
                pretty_structs=True,
                array_indexes=True,
                symbols=True,
                deref_refs=True))
        args_tree.add(arg_tree_name)
    return args_tree
