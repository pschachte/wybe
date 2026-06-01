class Node:
    def __init__(self, value, next=None):
        self.value = value
        self.next = next

    def append(self, other):
        # Appends other to the end of this list (non-destructive)
        if self.next is None:
            return other
        else:
            Node(self.value, self.next.append(other))

    def reverse_naive(self):
        # Returns a new reversed list (naive recursive, non-destructive)
        def rev(node):
            if node is None:
                return None
            if node.next is None:
                return Node(node.value)
            rest = rev(node.next)
            # Find the tail of the reversed rest and append current node
            tail = rest
            while tail.next:
                tail = tail.next
            tail.next = Node(node.value)
            return rest
        new_list = LinkedList()
        new_list.head = rev(self.head)
        return new_list

    def append_fresh(self, other):
        # Returns a new list that is the concatenation of self and other (non-destructive)
        def copy_nodes(node):
            if node is None:
                return None
            return Node(node.value, copy_nodes(node.next))
        new_head = copy_nodes(self.head)
        if not new_head:
            return other._copy()
        tail = new_head
        while tail.next:
            tail = tail.next
        tail.next = copy_nodes(other.head)
        new_list = LinkedList()
        new_list.head = new_head
        return new_list
