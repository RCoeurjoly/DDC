from typing import Optional, List, Tuple
import deal

# @deal.ensure(lambda left, right, result: result.startswith(left))
# @deal.ensure(lambda left, right, result: result.endswith(right))
# @deal.ensure(lambda left, right, result: len(result) == len(left) + len(right))
# def cat(left: str, right: str) -> str:
#     return left + right

class Node:
    def __init__(self, function_name: str, children:List['Node']) -> None:
        self.function_name = function_name # type: str
        self.children = children # type: List['Node']


@deal.post(lambda result: result >= 0)
#@deal.post(lambda result: result >= 0)
@deal.pure
def can_node_be_compressed(marked_execution_tree: 'Node') -> int:
    """Searches for the longest compression possible. Returns:
    - int: number of nodes that can be compressed. 0 if None"""
    if len(marked_execution_tree.children) != 1:
        return 0
    if marked_execution_tree.children[0].function_name != marked_execution_tree.function_name:
        return 0
    return can_node_be_compressed(marked_execution_tree.children[0]) + 1
