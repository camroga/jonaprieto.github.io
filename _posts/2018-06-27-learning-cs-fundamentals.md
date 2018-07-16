---
layout: "post"
title: "CS Basics"
date: "2018-06-27"
categories: learning
published: true
toc: true
---

Just for fun, let's to follow the [Brilliant](https://brilliant.org) chapters
about computer science.

## CS Fundamentals

### [x] [arrays](https://brilliant.org/practice/arrays/?chapter=intro-to-algorithms&p=2)
### [x] [searching](https://brilliant.org/practice/searching/?chapter=intro-to-algorithms)
### [x] [insertion-sort](https://brilliant.org/practice/insertion-sort/?chapter=intro-to-algorithms)
### [ ] [insertion-sort verified](https://wenkokke.github.io/2016/insertion-sort-in-agda/)
### [x] [big-o-notation](https://brilliant.org/practice/big-o-notation-2/?chapter=intro-to-algorithms)
### [x] [recursion](https://brilliant.org/practice/recursion/?chapter=recursion)

### [x] [cs-recursion](https://brilliant.org/practice/cs-recursion/?chapter=recursion)

Binary Search:
{%- highlight python -%}
def binary_search(A, item):
    if len(A) == 0:
        return False
    else:
        middle = len(A) // 2
        if A[middle] == item:
            return True
       # your code goes here
            return binary_search(A[:middle], item)
        else:
            return binary_search(A[middle + 1:], item)
list = [1, 2, 3, 5, 8, 22, 34, 42, 87, 103]
print(binary_search(list, 4))
print(binary_search(list, 42))
{%- endhighlight -%}


----

### [x] [divide-and-conquer](https://brilliant.org/practice/divide-and-conquer/?chapter=recursion)

Problem:

![](/assets/png-images/2018-06-27-learning-cs-fundamentals-b90ce6d8.png)

To solve this I conceive the square NxN divide in four small squares as follows.

```
[ N/2 ] | [ N/2 ]
--------@--------
[ N/2 ] | [ N/2 ]
```

The symbol (@) represents the origin. If we guess the point as the center we'll get information
about which is next of these small square we have to visit to find the diamond. Therefore, the next step
will be to solve the same problem with the half size of the original in case the last guess wasn't correct.

```
[ N/4 ] | [ N/4 ]
--------@--------
[ N/4 ] | [ N/4 ]
```

As you can see the maximum number of guessing will be depend on how many times we could divide by 2 the number N, that is, 2^#guesses-allowed. With ten guesses, N should be 1024, but we forgot one thing because the answer is 1023. There is a problem about the "center" because when N is odd, there is no such center.

----

### [x] [mergesort](https://brilliant.org/practice/mergesort/?chapter=recursion)

![](/assets/png-images/2018-06-27-learning-cs-fundamentals-299c445c.png)

{%- highlight python -%}
def merge(left, right):
    result = []
    left_idx, right_idx = 0, 0
    while left_idx < len(left) and right_idx < len(right):
        # change the direction of this comparison to change the direction of the sort
        if left[left_idx] <= right[right_idx]:
            result.append(left[left_idx])
            left_idx += 1
        else:
            result.append(right[right_idx])
            right_idx += 1

    if left:
        result.extend(left[left_idx:])
    if right:
        result.extend(right[right_idx:])
    return result

def merge_sort(m):
    if len(m) <= 1:
        return m

    middle = len(m) // 2
    left = m[:middle]
    right = m[middle:]

    left = merge_sort(left)
    right = merge_sort(right)
    return list(merge(left, right))
{%- endhighlight -%}

----
### [x] [quicksort](https://brilliant.org/practice/quicksort/?chapter=recursion)
Does the pivot always be in the correct position (sorted) after the first partitioning? Yes, it does.

{%- highlight python -%}
def quickSort(arr):
    less = []
    pivotList = []
    more = []
    arr_length = len(arr)
    if arr_length <= 1:
        return arr
    else:
        pivot = arr[0]
        for i in arr:
            if i < pivot:
                less.append(i)
            elif i > pivot:
                more.append(i)
            else:
                pivotList.append(i)
        less = quickSort(less)
        more = quickSort(more)
        return less + pivotList + more
{%- endhighlight -%}

### [x] [linked-list](https://brilliant.org/practice/linked-list/?chapter=recursion)

{%- highlight python -%}
def traverse(node):
    if node.next != null:
        traverse(node.next)
    print node.data
{%- endhighlight -%}

### [x] [stacks-and-queues](https://brilliant.org/practice/stacks-and-queues/?chapter=stacks-and-queues)

### [x] [stacks-2](https://brilliant.org/practice/stacks-2/?chapter=stacks-and-queues) - **LIFO** (Last-in First-out)


A **stack** is an *abstract data type* that places restrictions on where you can add and remove elements. As with any abstract data type, a stack can be implemented with a variety of data structures, such as a linked list or an array.

  - Review again this one: https://brilliant.org/practice/stacks-2/?p=10

----

### [x] [queues](https://brilliant.org/practice/queues/?chapter=stacks-and-queues) - **FIFO** (First-in first-out)

Circular queues

  ![](/assets/png-images/2018-06-27-learning-cs-fundamentals-d96247af.png)

  - ENQUEUE (Add data to the tail.)
  - DEQUEUE (Remove element from the head.)

A queue can be implemented using two stacks:

- The first stack if contains data, they are in the correct order. Popping out will return the tail of the queue. Otherwise if the data is in the other stack, this one will contain the data in reversed order. So, popping out will return us the head of the queue.

  ![](/assets/png-images/2018-06-27-learning-cs-fundamentals-b673ddb5.png)

### [ ] [binary-trees-2](https://brilliant.org/practice/binary-trees-2/?chapter=binary-trees)

  - The number of children each node has in a tree is called the branching factor
  - Each node has exactly one parent

  {%- highlight python -%}
   class Node:
     def __init__(self, value=None, left=None, right=None):
         self.value = value # information that is being stored in the tree
         self.left = left   # the left child (subtree)
         self.right = right # the right child (subtree)

     def __str__(self):
         return node.value
  {%- endhighlight -%}

  ![](/assets/png-images/2018-06-27-learning-cs-fundamentals-366895d9.png)

  - The **depth** of a node is the number of branches from the root to the node.
  - The **node height** is the number of branches from the node to the deepest leaf.
  - The **tree height** is the node height of the root, i.e. the number of branches along the longest path in the tree.


### [x] [binary-trees](https://brilliant.org/practice/binary-trees/?chapter=binary-trees)

  ![](/assets/png-images/2018-06-27-learning-cs-fundamentals-3e73c2fd.png)

  A **full binary tree** is a binary tree in which each node has exactly *zero or two children.*

  A **complete binary tree** is a binary tree in which every level, except possibly the last, is completely filled, and *all nodes are as far left as possible.*

  Note: A tree can be a full tree without being a complete tree, and a tree can be a complete tree without being a full tree.

### [x] [Traversals](https://brilliant.org/practice/traversals-2/?chapter=binary-trees)

TRAVERSALS

- Pre-order traversal (Root-Left-Right)

  {%- highlight python -%}
  def traverse(tree):
    if tree:
        print(tree.getRootVal())
        traverse(tree.getLeftChild())
        traverse(tree.getRightChild())
  {%- endhighlight -%}

- In-order traversal (Left-Root-Right)

  {%- highlight python -%}
  def traverse(tree):
      if tree:
          traverse(tree.getLeftChild())
          print(tree.getRootVal())
          traverse(tree.getRightChild())
  {%- endhighlight -%}

- Post-order traversal (Left-Right-Root)

  {%- highlight python -%}
  def traverse(tree):
      if tree:
          traverse(tree.getLeftChild())
          traverse(tree.getRightChild())
          print(tree.getRootVal())
  {%- endhighlight -%}


A **depth-first search**, or **DFS**, is the strategy that goes down a branch all the way until a leaf is reached, processes said branch, and then moves on to a different branch. This type of algorithm generally uses a **stack** in order to keep track of visited nodes, as the last node seen is the next one to be visited and the rest are stored to be visited later.

The **breadth-first search**, or **BFS**, is the counterpart to DFS in tree traversing techniques. It is a search algorithm that traverses down a tree using a queue as its data array, where elements are visited in a FIFO, first-in first-out, mechanism. This strategy is also called level-order traversal, as all nodes on a level are visited before proceeding to the next level.

### [ ] [binary-search-trees-2](https://brilliant.org/practice/binary-search-trees-2/?chapter=binary-trees)
### [ ] [tree-rotations](https://brilliant.org/practice/tree-rotations/?chapter=binary-trees)
### [ ] [red-black-trees](https://brilliant.org/practice/red-black-trees/?chapter=binary-trees)
### [ ] [heaps](https://brilliant.org/practice/heaps/?chapter=heaps-2)
### [ ] [priority-queues](https://brilliant.org/practice/priority-queues/?chapter=heaps-2)
### [ ] [binary-heaps](https://brilliant.org/practice/binary-heaps/?chapter=heaps-2)
### [ ] [heapsort](https://brilliant.org/practice/heapsort/?chapter=heaps-2)
### [ ] [treaps](https://brilliant.org/practice/treaps/?chapter=heaps-2)

## Algorithms

### [ ] [algorithms](https://brilliant.org/practice/algorithms/?chapter=algorithms)
### [ ] [intro-to-computation](https://brilliant.org/practice/intro-to-computation/?chapter=algorithms)
### [ ] [a-naive-approach](https://brilliant.org/practice/a-naive-approach/?chapter=algorithms)
### [ ] [real-world-application](https://brilliant.org/practice/real-world-application/?chapter=algorithms)
### [ ] [sorting](https://brilliant.org/practice/sorting/?chapter=sorting)
### [ ] [introduction-to-sorting](https://brilliant.org/practice/introduction-to-sorting/?chapter=sorting)
### [ ] [insertion-sort-2](https://brilliant.org/practice/insertion-sort-2/?chapter=sorting)
### [ ] [mergesort-2](https://brilliant.org/practice/mergesort-2/?chapter=sorting)
### [ ] [quicksort-2](https://brilliant.org/practice/quicksort-2/?chapter=sorting)
### [ ] [radix-sort](https://brilliant.org/practice/radix-sort/?chapter=sorting)
### [ ] [graphs](https://brilliant.org/practice/graphs/?chapter=graphs-2)
### [ ] [introduction-to-graphs](https://brilliant.org/practice/introduction-to-graphs/?chapter=graphs-2&p=1)
### [ ] [trees-2](https://brilliant.org/practice/trees-2/?chapter=graphs-2)
### [ ] [breadth-first-search-2](https://brilliant.org/practice/breadth-first-search-2/?chapter=graphs-2)
### [ ] [minimum-spanning-trees](https://brilliant.org/practice/minimum-spanning-trees/?chapter=graphs-2)
### [ ] [strings](https://brilliant.org/practice/strings/?chapter=strings-2)
### [ ] [introduction-to-string-algorithms](https://brilliant.org/practice/introduction-to-string-algorithms/?chapter=strings-2)
### [ ] [substring-search-algorithms](https://brilliant.org/practice/substring-search-algorithms/?chapter=strings-2)
### [ ] [deterministic-finite-automaton](https://brilliant.org/practice/deterministic-finite-automaton/?chapter=strings-2)
### [ ] [knuth-morris-pratt-algorithm](https://brilliant.org/practice/knuth-morris-pratt-algorithm/?chapter=strings-2)
### [ ] [tries-2](https://brilliant.org/practice/tries-2/?chapter=strings-2)
### [ ] [dynamic-programming](https://brilliant.org/practice/dynamic-programming/?chapter=dynamic-programming-2)
### [ ] [dynamic-programming-introduction](https://brilliant.org/practice/dynamic-programming-introduction/?chapter=dynamic-programming-2)
### [ ] [dynamic-programming-tiling-problem](https://brilliant.org/practice/dynamic-programming-tiling-problem/?chapter=dynamic-programming-2)
### [ ] [dynamic-programming-binary-tree](https://brilliant.org/practice/dynamic-programming-binary-tree/?chapter=dynamic-programming-2)
### [ ] [dynamic-programming-envelopes](https://brilliant.org/practice/dynamic-programming-envelopes/?chapter=dynamic-programming-2&p=1)

## Computer Memory

### [x] [introduction-to-memory](https://brilliant.org/practice/introduction-to-memory/?chapter=introduction-to-memory)
### [x] [storing-data-in-a-computer](https://brilliant.org/practice/storing-data-in-a-computer/?chapter=introduction-to-memory)
### [ ] [working-in-binary-decimal-and-hexadecimal](https://brilliant.org/practice/working-in-binary-decimal-and-hexadecimal/?chapter=introduction-to-memory)
### [ ] [linear-memory-model](https://brilliant.org/practice/linear-memory-model/?chapter=introduction-to-memory)
### [ ] [memory-layout](https://brilliant.org/practice/memory-layout/?chapter=introduction-to-memory)
### [ ] [courses/memory/memory-of-programs/](https://brilliant.org/courses/memory/memory-of-programs/)
### [ ] [memory-of-programs](https://brilliant.org/practice/memory-of-programs/?chapter=memory-of-programs)
### [ ] [the-source-file-compiler-and-executable-file](https://brilliant.org/practice/the-source-file-compiler-and-executable-file/?chapter=memory-of-programs)
### [ ] [memory-segments](https://brilliant.org/practice/memory-segments/?chapter=memory-of-programs)
### [ ] [the-code-segment-and-static-segment](https://brilliant.org/practice/the-code-segment-and-static-segment/?chapter=memory-of-programs)
### [ ] [the-stack-segment](https://brilliant.org/practice/the-stack-segment/?chapter=memory-of-programs)
### [ ] [the-heap-segment](https://brilliant.org/practice/the-heap-segment/?chapter=memory-of-programs)
### [ ] [virtual-memory](https://brilliant.org/practice/virtual-memory/?chapter=virtual-memory)
### [ ] [processes](https://brilliant.org/practice/processes/?chapter=virtual-memory)
### [ ] [virtual-memory-and-physical-memory](https://brilliant.org/practice/virtual-memory-and-physical-memory/?chapter=virtual-memory)
### [ ] [memory-pages](https://brilliant.org/practice/memory-pages/?chapter=virtual-memory)
### [ ] [mmu-and-the-os](https://brilliant.org/practice/mmu-and-the-os/?chapter=virtual-memory)
### [ ] [techniques-for-performance](https://brilliant.org/practice/techniques-for-performance/?chapter=techniques-for-performance)
### [ ] [page-cache](https://brilliant.org/practice/page-cache/?chapter=techniques-for-performance)
### [ ] [memory-mapping](https://brilliant.org/practice/memory-mapping/?chapter=techniques-for-performance)
### [ ] [demand-load](https://brilliant.org/practice/demand-load/?chapter=techniques-for-performance)
### [ ] [page-sharing-and-copy-on-write](https://brilliant.org/practice/page-sharing-and-copy-on-write/?chapter=techniques-for-performance)
### [ ] [shared-libraries](https://brilliant.org/practice/shared-libraries/?chapter=shared-libraries)
### [ ] [libraries](https://brilliant.org/practice/libraries/?chapter=shared-libraries)
### [ ] [relocation](https://brilliant.org/practice/relocation/?chapter=shared-libraries)
### [ ] [position-independent-code](https://brilliant.org/practice/position-independent-code/?chapter=shared-libraries)
### [ ] [procedure-linkage-table](https://brilliant.org/practice/procedure-linkage-table/?chapter=shared-libraries)
### [ ] [caching](https://brilliant.org/practice/caching/?chapter=caching)
### [ ] [caching-overview](https://brilliant.org/practice/caching-overview/?chapter=caching)
### [ ] [details-of-caching](https://brilliant.org/practice/details-of-caching/?chapter=caching)
### [ ] [practice-uses-of-caching](https://brilliant.org/practice/practice-uses-of-caching/?chapter=caching)
### [ ] [dram-sram-and-cpu-caches](https://brilliant.org/practice/dram-sram-and-cpu-caches/?chapter=caching)
### [ ] [computer-memory-architecture](https://brilliant.org/practice/computer-memory-architecture/?chapter=caching)


### [Additional Practice](https://brilliant.org/computer-science/)

#### Types and Data Structures

- [ ] Computer Science Warmups
- [ ] Abstract Data Types
- [ ] Linear Data Structures
- [ ] Hash-Based Data Structures
- [ ] Trees
- [ ] Binary Search Trees
- [ ] Heaps
- [ ] Graphs
- [ ] Strings

#### Algorithms

- [ ] Introduction to Algorithms
- [ ] Complexity / Runtime Analysis
- [ ] Dynamic Programming
- [ ] Sorting Algorithms
- [ ] Graph Algorithms
- [ ] Flow Networks
- [ ] String Algorithms
- [ ] Computational Geometry
- [ ] Computability
- [ ] Signals and Systems

#### Programming Languages
- [ ] Functions
- [ ] Loops
- [ ] Conditionals
- [ ] Object-Oriented Programming
- [ ] Functional Programming

#### Cryptography and Simulations
- [ ] Cryptography
- [ ] Simulation Techniques

#### Machine Learning
- [ ] Introduction to Machine Learning
- [ ] Classification
- [ ] Clustering
- [ ] Modelling
- [ ] Recommendation
- [ ] Artificial Neural Networks
