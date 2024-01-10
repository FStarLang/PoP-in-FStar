.. _Pulse_linked_list:

Linked Lists
============

In this chapter, we develop a linked list library. Along the way,
we'll see uses of recursive predicates, trades, and universal
quantification.

Representing a Linked List
..........................

Let's start by defining the type of a singly linked list:

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: fstar
   :start-after: //llist$
   :end-before: //llist$

A ``node t`` contains a ``head:t`` and a ``tail:llist t``, a nullable
reference pointing to the rest of the list. Nullable references are
represented by an option, as :ref:`we saw before
<Pulse_nullable_ref_helpers>`.

Next, we need a predicate to relate a linked list to a logical
representation of the list, for use in specifications. 

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: fstar
   :start-after: //is_list$
   :end-before: //is_list$

The predicate ``is_list x l`` is a recursive predicate:

  * When ``l == []``, the reference ``x`` must be null.

  * Otherwise, ``l == head :: tl``, ``x`` must contains a valid
    reference ``p``, where ``p`` points to ``{ head; tail }`` and,
    recursively , we have ``is_list tail tl``.


Boilerplate: Introducing and Eliminating ``is_list``
....................................................

We've seen :ref:`recursive predicates in a previous chapter
<Pulse_recursive_predicates>`, and just as we did there, we need some
helper ghost functions to work with ``is_list``. We expect the Pulse
checker will automate these boilerplate ghost lemmas in the future,
but, for now, we are forced to write them by hand.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //boilerplate$
   :end-before: //boilerplate$



Case analyzing a nullable pointer
.................................

When working with a linked list, the first thing we'll do, typically,
is to check whether a given ``x:llist t`` is null or not. However, the
``is_list x l`` predicate is defined by case analysing ``l:list t``
rather than ``x:llist t``, since that is makes it possible to write
the predicate by recursing on the tail of ``l``. So, below, we have a
predicate ``is_list_cases x l`` that inverts ``is_list x l`` predicate
based on whether or not ``x`` is null.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: fstar
   :start-after: //is_list_cases$
   :end-before: //is_list_cases$

Next, we define a ghost function to invert ``is_list`` into ``is_list_cases``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //cases_of_is_list$
   :end-before: ```

We also define two more ghost functions that package up the call to
``cases_of_is_list``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //is_list_case_none$
   :end-before: ```

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //is_list_case_some$
   :end-before: ```

Length, Recursively
...................

With our helper functions in hand, let's get to writing some real
code, starting with a function to compute the length of an ``llist``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //length$
   :end-before: ```

The ``None`` case is simple.

Some points to note in the ``Some`` case:

  * We use ``with _node _tl. _`` to "get our hands on" the
    existentially bound witnesses.

  * After reading ``let node = !vl``, we need ``is_list node.tail
    _tl`` to make the recursive call. But the context contains
    ``is_list _node.tail _tl`` and ``node == _node``. So, we need a
    rewrite.

  * We re-introduce the ``is_list`` predicate, and return ``1 +
    n``. While the ``intro_is_list_cons x vl`` is a ghost step and
    will be erased before execution, the addition is not---so, this
    function is not tail recursive.

Exercise 1
..........

Write a tail-recursive version of ``length``.
    
Exercise 2
..........

Index the ``is_list`` predicate with a fractional permission.  Write
ghost functions to share and gather fractional ``is_list`` predicates.

Length, Iteratively, with Trades
................................

What if we wanted to implement ``length`` using a while loop, as is
more idiomatic in a language like C. It will take us a few steps to
get there, and we'll use the trade operator (``@==>``) to structure
our proof.

Trade Tails
+++++++++++

Our first step is to define ``tail_for_cons``, a lemma that with
permission on a node pointer (``pts_to v n``), we can build a trade
transforming a permission on the tail into a permission for a cons
cell starting at the given node.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //tail_for_cons$
   :end-before: ```


Tail of a list
++++++++++++++

Next, here's a basic operation on a linked list: given a pointer to a
cons cell, return a pointer to its tail. Here's a small diagram:


.. code-block::

   x             tl
   |             |
   v             v
   .---.---.     .---.---.
   |   | --|---> |   | --|--> ...
   .---.---.     .---.---.

We're given a pointer ``x`` to the cons cell at the head of a list,
and we want to return ``tl``, the pointer to the next cell (or
``None``, of x this is the end of the list). But, if we want to return
a pointer to ``tl``, we a permission accounting problem:

  * We cannot return permission to ``x`` to the caller, since then we
    would have two *aliases* pointing to the next cell in the list:
    the returned ``tl`` and ``x -> next``.

  * But, we cannot consume the permission to ``x`` either, since we
    would like to return permission to ``x`` once the return ``tl``
    goes out of scope.

The solution here is to use a trade. The type of ``tail`` below says
that if ``x`` is a non-null pointer satisfying ``is_list x 'l``, then
``tail`` returns a pointer ``y`` such that ``is_list y tl`` (where
``tl`` is the tail of ``'l``); and, one can trade ``is_list y tl`` to
recover permission to ``is_list x 'l``. The trade essentially says
that you cannot have permission to ``is_list x 'l`` and ``is_list y
tl`` at the same time, but once you give up permission on ``y``, you
can get back the original permission on ``x``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //tail$
   :end-before: ```

``length_iter``
+++++++++++++++

The code below shows our iterative implementation of ``length``. The
basic idea is simple , thorugh the proof takes a bit of doing. We
initialize a current pointer ``cur`` to the head of the list; and
``ctr`` to ``0``. Then, while ``cur`` is not null, we move ``cur`` to
the tail and increment ``ctr``. Finally, we return the ``!ctr``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //length_iter$
   :end-before: ```

Now, for the proof. The main part is the loop invariant, which says:

  * the current value of the counter is ``n``;
    
  * ``cur`` holds a list pointer, ``ll`` where ``ll`` contains the
    list represented by ``suffix``;

  * ``n`` is the the length of the prefix of the list traversed so far;

  * the loop continues as long as ``b`` is true, i.e., the list
    pointer ``l`` is not ``None``;

  * and, the key bit: you can trade ownership on ``ll`` back for
    ownership on the original list ``x``.

Some parts of this could be simplified, e.g., to avoid some of the
rewrites.

One way to understand how trades have helped here is to compare
``length_iter`` to the recursive function ``length``. In ``length``,
after each recursive call returns, we called a ghost function to
repackage permission on the cons cell after taking out permission on
the tail. The recursive function call stack kept track of all these
pieces of ghost code that had to be executed. In the iterative
version, we use the trade to package up all the ghost functions that
need to be run, rather than using the call stack. When the loop
terminates, we use ``I.elim`` to run all that ghost code at once.

Of course, the recursive ``length`` is much simpler in this case, but
this pattern of using trades to package up ghost functions is quite
broadly useful.

Append, Recursively
...................


Append, Iteratively
...................
