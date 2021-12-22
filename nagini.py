from typing import Optional, List, Tuple
from nagini_contracts.contracts import *

class Node:
    def __init__(self, function_name: str, children:List['Node']) -> None:
        self.function_name = function_name # type: str
        self.children = children # type: List['Node']
        Ensures(Acc(self.function_name) and self.function_name is function_name and
                Acc(self.children) and self.children is children)

@Pure
def can_node_be_compressed(marked_execution_tree: 'Node') -> Tuple[bool, int]:
    """Searches for the longest compression possible. Returns:
    - bool: True if can be compressed. False otherwise
    - int: If it can be compressed, number of nodes to compress"""
    Requires(Acc(marked_execution_tree.children, 1/2))
    Requires(Acc(list_pred(marked_execution_tree.children)))
    Requires(Forall(int, lambda i: Implies(i >= 0 and i < len(marked_execution_tree.children), Acc(marked_execution_tree.children[i].function_name))))
    Requires(Acc(marked_execution_tree.function_name, 1/2))
    # Ensures(Implies(Result()[1] == 0, Result()[0] is False))
    # Ensures(Implies(Result()[1] > 0, Result()[0] is True))
    if len(marked_execution_tree.children) != 1:
        return False, 0
    if marked_execution_tree.children[0].function_name != marked_execution_tree.function_name:
        return False, 0
    _, downstream_length = can_node_be_compressed(marked_execution_tree.children[0])
    return True, downstream_length + 1
