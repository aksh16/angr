from node import *
from interval import *


class IntervalTree(object):
    def __init__(self):
        self.root = Root()
        self.n = 0

    def add(self, interval):
        self.n += 1
        if self.root.child is None:
            self.root.child = Node(interval, interval.end, self.root)
        else:
            self.root.child.add(interval)

    # Replace all addi with creating interval and add
    def addi(self, begin, end, data=None):
        i = Interval(begin, end, data)
        self.add(i)

    def search(self, begin, end=None):
        if end is None:
            if isinstance(begin, Interval):
                interval = begin
            elif type(begin) in (int, long):
                ris = []
                self.root.child.search_point(begin, ris)
                return ris
            else:
                raise Exception("search(): wrong types")
        else:
            assert type(begin) in (int, long) and type(end) in (int, long) and begin <= end
            interval = Interval(begin, end)

        if self.root.child is None:
            return []
        ris = []
        self.root.child.search(interval, ris)
        return ris

    def __iter__(self):
        if self.root.child is not None:
            stack = [self.root.child]
            while stack:
                el = stack.pop()
                yield el.interval
                if el.left_child is not None:
                    stack.append(el.left_child)
                if el.right_child is not None:
                    stack.append(el.right_child)

    def __len__(self):
        return self.n

    def _copy(self, node, new_tree_node):
        if node is None:
            return
        if isinstance(node, Root):
            new_tree_node.child = Node(node.child.interval.copy(), node.child.max, new_tree_node)
            new_tree_node.child.left_depth = node.child.left_depth
            new_tree_node.child.right_depth = node.child.right_depth
        else:
            if node.left_child is None:
                new_tree_node.left_child = None
            else:
                new_tree_node.left_child = Node(node.left_child.interval.copy(), node.left_child.max, new_tree_node)
                new_tree_node.left_child.left_depth = node.left_child.left_depth
                new_tree_node.left_child.right_depth = node.left_child.right_depth
            if node.right_child is None:
                new_tree_node.right_child = None
            else:
                new_tree_node.right_child = Node(node.right_child.interval.copy(), node.right_child.max, new_tree_node)
                new_tree_node.right_child.left_depth = node.right_child.left_depth
                new_tree_node.right_child.right_depth = node.right_child.right_depth

    def copy(self):
        new_tree = IntervalTree()
        self._copy(self.root, new_tree.root)
        return new_tree
