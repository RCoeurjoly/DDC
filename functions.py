def general_debugging_algorithm(marked_execution_tree, strategy):
    while (marked_execution_tree is not None
           or (marked_execution_tree.iscorrect == Answer.NO
               and len(marked_execution_tree.children) == 0)):
        selected_node = select_node(marked_execution_tree, strategy)
        answer = ask_about_node(selected_node)
        selected_node.iscorrect = answer
        if (answer == Answer.NO):
            marked_execution_tree = selected_node
        elif (answer == Answer.YES):
            pass
        elif (answer == Answer.TRUSTED):
            pass
        elif (answer == Answer.IDK):
            pass
    return marked_execution_tree

def select_node(marked_execution_tree, strategy):
    return strategy(marked_execution_tree)

def update_nodes_weight(nodes, position):
    node_and_parents_positions = [position[:len(position)-n] for n in range(len(position))]
    for node_position in node_and_parents_positions:
        get_node_from_position(nodes,
                               node_position).weight += 1

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
    gen = (node for node in nodes if node.iscorrect == Answer.IDK)
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

def top_down_strategy(marked_execution_tree):
    if (marked_execution_tree.iscorrect == ANSWER.IDK):
        return marked_execution_tree, True
    else:
        for child in marked_execution_tree.children:
            tmp_marked_execution_tree, found = top_down_strategy(child)
            if found:
                return tmp_marked_execution_tree, found

def divide_and_query_Shapiro_strategy(node):
    # We select the child node whose weight is the closest to w(n)/2
    # w(child node) being >= w(n)/2
    for child in node.children:
        child.weight
    pass

def divide_and_query_Hirunkitti_strategy(node):
    # We select the child node whose weight is the closest to w(n)/2
    # w(child node) being >= w(n)/2
    # or w(child node) being <= w(n)/2
    distance = node.weight/2
    choosen_node = node
    for child in node.children:
        if abs(child.weight - node.weight/2) < distance:
            distance = abs(child.weight - node.weight/2)
            choosen_node = child
    return choosen_node

def ask_about_node(node):
    print("Is the following node correct?")
    print(node.get_tree(False))
    options = ["Yes", "No", "I don't know", "Trusted"]
    terminal_menu = TerminalMenu(options)
    menu_entry_index = terminal_menu.show()
    return options[menu_entry_index]

def get_node_from_position(nodes, position):
    if len(position) == 1:
        return nodes[position[0]]
    return get_node_from_position(nodes[position[0]].children, position[1:])

def get_node_from_frame(nodes, frame):
    for node in nodes:
        if node.frame == frame and node.arguments_when_returning == []:
            return node
    return get_node_from_frame(nodes[-1].children, frame)

def get_last_node(nodes):
    if nodes == []:
        return None
    if nodes[-1].childrenildren == []:
        return nodes[-1]
    return get_last_node(nodes[-1].children)
