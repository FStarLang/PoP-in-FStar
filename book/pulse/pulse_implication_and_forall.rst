.. _Pulse_implication_and_forall:

Implication and Universal Quantification
========================================

In this chapter, we'll learn about two more separation logic
connectives, ``@==>`` and ``forall*``. We'll explain how they work in
the context of a linked list library.

Representing a Linked List
..........................

Let's start by defining the type of a singly linked list:

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //llist$
   :end-before: //llist$

A ``node t`` contains a ``head:t`` and a ``tail:llist t``, a nullable
reference pointing to the rest of the list. Nullable references are
represented by an option, as :ref:`we saw before
<Pulse_nullable_ref_helpers>`.

Next, we need a predicate to relate a linked list to a logical
representation of the list, for use in specifications. 

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //is_list$
   :end-before: //is_list$

The predicate ``is_list x l`` is a recursive predicate:

  * When ``l == []``, the reference ``x`` must be null.

  * Otherwise, ``l == head :: tl``, ``x`` must contains a valid
    reference ``p``, where ``p`` points to ``{ head; tail }`` and,
    recursively , we have ``is_list tail tl``.


Boilerplate: Introducing and Eliminating ``is_list``
++++++++++++++++++++++++++++++++++++++++++++++++++++

We've seen :ref:`recursive predicates in a previous chapter
<Pulse_recursive_predicates>`, and just as we did there, we need some
helper ghost functions to work with ``is_list``. We expect the Pulse
checker will automate these boilerplate ghost lemmas in the future,
but, for now, we are forced to write them by hand.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //boilerplate$
   :end-before: //boilerplate$



Case analyzing a nullable pointer
+++++++++++++++++++++++++++++++++

When working with a linked list, the first thing we'll do, typically,
is to check whether a given ``x:llist t`` is null or not. However, the
``is_list x l`` predicate is defined by case analysing ``l:list t``
rather than ``x:llist t``, since that is makes it possible to write
the predicate by recursing on the tail of ``l``. So, below, we have a
predicate ``is_list_cases x l`` that inverts ``is_list x l`` predicate
based on whether or not ``x`` is null.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //is_list_cases$
   :end-before: //is_list_cases$

Next, we define a ghost function to invert ``is_list`` into ``is_list_cases``.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //cases_of_is_list$
   :end-before: ```

We also define two more ghost functions that package up the call to
``cases_of_is_list``.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //is_list_case_none$
   :end-before: ```

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //is_list_case_some$
   :end-before: ```

Length, Recursively
+++++++++++++++++++

With our helper functions in hand, let's get to writing some real
code, starting with a function to compute the length of an ``llist``.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
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
++++++++++

Write a tail-recursive version of ``length``.
    
Exercise 2
++++++++++

Index the ``is_list`` predicate with a fractional permission.  Write
ghost functions to share and gather fractional ``is_list`` predicates.

Length, Iteratively, with ``@==>``
++++++++++++++++++++++++++++++++++

What if we wanted to implement ``length`` using a while loop, as is
more idiomatic in a language like C. It will take us a few steps to
get there, and we'll use the ``@==>`` operator to structure our proof.

The library ``module I = Pulse.Lib.Stick.Util`` defines the operator
``(@==>)`` and utilities for using it. Here's an informal description
of what it means:

``p @==> q`` says that if you have ``p`` then you can *trade* it for
``q``. In other words, from ``p ** (p @==> q)``, you can derive
``q``. This step of reasoning is performed using a ghost function
``I.elim`` with the signature below:

.. code-block:: pulse    
   
   ghost
   fn I.elim (p q:vprop)
   requires p ** (p @==> q)
   ensures q
   

For now, think of ``p @==> q`` as a kind of implication in separation
logic and ``I.elim`` as implication elimination. Importantly, if you
think of ``p`` as describing permission on a resource, the ``I.elim``
makes you *give up* the permission ``p`` and get ``q`` as a
result. Note, during this step, you also lose permission on the
implication, i.e., ``p @==> q`` lets you trade ``p`` for ``q`` just
once.

But, how to you create a ``p @==> q`` in the first place? That's its
introducion form, shown below:

.. code-block:: pulse

   ghost
   fn I.intro (p q r:vprop) (elim: ()

