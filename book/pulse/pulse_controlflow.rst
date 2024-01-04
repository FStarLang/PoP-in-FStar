.. _Pulse_ControlFlow:

Conditionals, Loops, and Recursion
==================================

To start writing interesting programs, we need a few control
constructs. In this chapter, we'll write our first while loops,
conditionals, and recursive programs.


Conditionals
............

Here's a simple program that returns the maximum value stored in two
references.

.. literalinclude:: ../code/pulse/PulseTutorial.ControlFlow.fst
   :language: pulse
   :start-after: //SNIPPET_START: max$
   :end-before: //SNIPPET_END: max$

This program illustrates a very common specification style.

  * We have a pure, F* function ``max_spec``

  * And a Pulse function working on mutable references, with a
    specification that relates it to the pure F* spec. In this case,
    we prove that ``max`` behaves like ``max_spec`` on the logical
    values that witness the contents of the two references.

The implementation of ``max`` uses a Pulse conditional statement. Its
syntax is different from the F* ``if-then-else`` expression: Pulse
uses a more imperative syntax with curly braces, which should be
familiar from languages like C.

Limitation: Non-tail Conditionals
+++++++++++++++++++++++++++++++++

Pulse's inference machinery does not yet support conditionals that
appear in non-tail position. For example, this variant of ``max``
fails, with the error message shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.ControlFlow.fst
   :language: pulse
   :start-after: ```pulse //max_alt_fail$
   :end-before: ```

.. code-block::                 

   Pulse cannot yet infer a postcondition for a non-tail conditional statement;
   Either annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional

Here's an annotated version of ``max_alt`` that succeeds.

.. literalinclude:: ../code/pulse/PulseTutorial.ControlFlow.fst
   :language: pulse
   :start-after: ```pulse //max_alt$
   :end-before: ```

We are working on adding inference for non-tail conditionals.

Pattern matching
................



While loops
...........



Recursion
.........
