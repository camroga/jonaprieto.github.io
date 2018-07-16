---
layout: "post"
title: "Concurrency"
date: "2018-06-27"
categories: learning
published: true
toc: true
---


## Keywords

![](/assets/png-images/2018-06-27-concurrent-programming-5d8141a7.png)

- A **sequential algorithm** is a *formal description* of the behaviour of a
  sequential state machine: the text of the algorithm states the transitions
  that have to be sequentially executed.

- An **algorithm** is a text that describes statements that have to be executed

- A **process** is a “text in action” that results from the algorithm

- A **sequential process** (sometimes called a **thread**) is a process defined
  by a single control flow (i.e., its behavior is managed by a single program
  counter).

- A **concurrent algorithm** (or *concurrent program* or *multiprocess program*)
  is the description of *a set of sequential state machines* that cooperate
  through a communication medium, e.g., a **shared memory**.

We consider process that are:

  - *“Reliable”* means that each process results from the correct execution of
  - the code of the corresponding algorithm

  - *“Asynchronous”* means that there is no timing assumption on the time it
    takes for a process to proceed from a state transition to the next one
    (which means that an asynchronous sequential process proceeds at an
    arbitrary speed).

## Process Synchronization

Processes of a multiprocess program **interact** in one way or another

Assumptions:

1. one processor per process
2. consequently the processes do execute *in parallel*

This assumption on the number of processors means that, when there are fewer
processors than processes, there is an **underlying scheduler** (hidden to the
processes) that assigns processors to processes.

*Process synchronization* occurs when the progress of one or several processes
*depends on the behavior of other processes.

Two types of process interaction require synchronization: *competition* and
*cooperation*

- **Synchronization** is the *set of rules* and *mechanisms* that allows the
  specification and implementation of sequencing properties on statements issued
  by the processes so that all the executions of a multiprocess program are
  correct

### Synchronization: Competition

This type of process interaction occurs when processes have to compete to
execute some statements and only one process at a time (or a bounded number of
them) is allowed to execute them

- Example: *resource allocation is a typical example of process competition*.


## Video lectures

### [C++11 Concurrency by Bartosz Milewski](https://www.youtube.com/watch?v=80ifzK3b8QQ&list=PL1835A90FC78FF8BE)

- [ ] [1. Preliminaries, "Hello Thread!," fork/join](https://www.youtube.com/watch?v=80ifzK3b8QQ)
- [ ] [2. Move semantics, passing arguments to threads](https://www.youtube.com/watch?v=qtRUG5ztMoA)
- [ ] [3. Sharing data between threads](https://www.youtube.com/watch?v=TZ9BgdgpYm8)
- [ ] [4. Promises, futures, and async](https://www.youtube.com/watch?v=o0pCft99K74)
- [ ] [5. Async tasks, task-based concurrency](https://www.youtube.com/watch?v=_Ll0PIobErE)
- [ ] [6. Map/Reduce. Massively parallel directory listing.](https://www.youtube.com/watch?v=2Xad9bCYbJE)
- [ ] [7. Mutexes, locks, and monitors](https://www.youtube.com/watch?v=4zWbQRE3tWk)
- [ ] [8. Argument passing. Chasing a concurrency bug.](https://www.youtube.com/watch?v=frPBwUDGLEI)
- [ ] [9. Condition variables](https://www.youtube.com/watch?v=309Y-QlIvew)
- [ ] [The Language of Concurrency General introduction to concurrency](https://www.youtube.com/watch?v=dB4kAO8M5Fg)


### [Haskell and Concurrency by Bartosz Milewski](https://www.youtube.com/watch?v=80ifzK3b8QQ&list=PL1835A90FC78FF8BE)

Probably to star watching from the video 5-1.

- [ ] [1-1 Why Haskell?](https://www.youtube.com/watch?v=N6sOMGYsvFA)
- [ ] [1-2 Functions](https://www.youtube.com/watch?v=ybba5tcOeEY)
- [ ] [2-1 More Functions](https://www.youtube.com/watch?v=oQ4fvA1OEcY)
- [ ] [2-2 Product data types](https://www.youtube.com/watch?v=a6IkhX1zgXI)
- [ ] [3-1 Laziness](https://www.youtube.com/watch?v=jWrRs-l8C1U)
- [ ] [3-2 Sum types](https://www.youtube.com/watch?v=MagayXbH4oY)
- [ ] [4-1 Recursion](https://www.youtube.com/watch?v=F-nAAIH4e2s)
- [ ] [4-2 Functors](https://www.youtube.com/watch?v=tVK7mzD4PVQ)
- [ ] [5-1 Monads!](https://www.youtube.com/watch?v=PlFgKV0ZXoE)
- [ ] [5-2 The Monad Class](https://www.youtube.com/watch?v=UtNB30Na65g)
- [ ] [6-1 IO Monad](https://www.youtube.com/watch?v=h6zbQ23U05g)
- [ ] [6-2 Parallellism and Concurrency](https://www.youtube.com/watch?v=FdUS93RXEwY)
- [ ] [7 1 The Eval monad](https://www.youtube.com/watch?v=3NjxfKsjn-k)
- [ ] [7-2 Parallel sudoku solver, strategies, overview of Haskell parallelism.](https://www.youtube.com/watch?v=ynEhy_zAL_0)
- [ ] [8-1 Concurrent Haskell, MVars](https://www.youtube.com/watch?v=Y5UiylhFzhI)
- [ ] [8-2 Software Transactional Memory](https://www.youtube.com/watch?v=GIimRbcOvM8)
