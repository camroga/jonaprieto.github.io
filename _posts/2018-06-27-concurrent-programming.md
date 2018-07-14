---
layout: "post"
title: "Concurrent"
date: "2018-06-27"
categories: learning
published: true
toc: true
---

![](/assets/png-images/2018-06-27-concurrent-programming-5d8141a7.png)

## Keywords

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
