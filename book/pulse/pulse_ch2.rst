.. _Pulse_References:

Mutable References
==================

Pulse aims to support programming with explicit control over memory
management and without need for a garbage collector, similar to
languages like C or Rust, but, of course, in a proof-oriented style.
Towards that end, one of the main features it offers (especially in
comparison to purely functional F*) is support for references to
mutable memory. In this chapter, we'll learn about three kinds of
mutable references: stack references, heap references (or boxes), and
ghost references. Stack references point to memory allocated in the
stack frame of the current function (in which case the memory is
reclaimed when the function returns). Heap references, or boxes, point
to memory locations in the heap, and heap memory is explicitly
reclaimed by calling ``drop`` or ``free``. Ghost references are for
specification and proof purposes only and point to memory locations
that do not really exist at runtime.


Stack references
^^^^^^^^^^^^^^^^

We have already seen the type ``ref t``, as in the ``incr`` function
below: the type ``ref t`` is the type of a memory reference that
typically refers to a memory location on the stack (though, we'll soon
see that it may also be used to refer to memory on the heap).

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //incr
   :end-before: ```


``let mut`` creates a new stack ref
...................................

To create a new ``ref t``, one uses the ``let mut`` construct of
Pulse, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //one
   :end-before: ```

The body of the program is annotated to show program assertions that
are true after each command.

  * Initially, only the precondition ``emp`` is valid.

  * After ``let mut i = 0``, we have ``i : ref int`` and ``pts_to i
    0``, meaning that ``i`` points to a stack slot that holds the
    value ``0``.

  * After calling ``incr i``, we have ``pts_to i (0 + 1)``

  * Finally, we dereference ``i`` using ``!i`` and return ``v:int``
    the current value of ``i`` at which point the scope of ``i`` ends
    and the memory it points to is reclaimed. The final assertion
    corresponds to the postcondition of ``one``.

A few additional points to note here:

  * Pulse proves ``pure`` properties automatically, by sending queries
    to the SMT solver.

  * Pulse simplifies ``vprop`` implicitly, e.g., Pulse will
    automatically rewrite ``emp ** p`` to ``p``.

  * Like F*, Pulse tries to instantiate implicit arguments
    automatically, e.g., at the call to ``incr``, Pulse automatically
    instantiates ``'v`` to ``0`` (actually, to ``hide 0``).

Stack references are scoped and implicitly reclaimed
....................................................

To emphasize that stack references allocted with ``let mut`` are
scoped, let's look at the program below that Pulse refuses to check:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //refs_as_scoped FAIL
   :end-before: ```

The error points to the location of ``s`` with the message below,
meaning that the current assertion on the heap is only ``emp``, while
the goal to be proven for the postcondition is ``pts_to s 0``. In
other words, we no longer have ownership on ``s`` once it goes out of
scope.

.. code-block::

  - Cannot prove:
      pts_to s 0
  - In the context:
      emp

Dereferencing is explicit
.........................

Unlike languages like C or Rust which make a distinction between
l-values and r-values and implicitly read the content of references,
in Pulse (like in OCaml), references are explicitly dereferenced. [#]_
As the program below illustrates, references themselves can be passed
to other functions (e.g., as in/out-parameters) while their current
values must be passed expliclity.

The function ``add`` takes both a refrence ``r:ref int`` and a value
``n:int`` as arguments:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //add
   :end-before: ```

Meanwhile, the function ``four`` allocates a new stack reference ``i``
initialized to ``1``; calls ``add`` twice to double the value stored
in ``i`` each time.
                
.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //four
   :end-before: ```

Note, Pulse expects the results of all stateful operations to be
explicitly ``let``-bound. For example, the following code fails to
type checked:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //four FAIL
   :end-before: ```

.. code-block::

  - Expected type "int"; but "!i" has type
    "stt int
         (pts_to i (reveal (*?u93*) _))
         (fun x -> pts_to i x ** pure (reveal (*?u93*) _ == x))"

The error points to the first occurrence of ``(!i)``. The message is
admittedly cryptic and should be improved. As we'll see in a later
chapter, the type ``stt _ _ _`` is the type of an unevaluated Pulse
comptuation---this error complains that ``add`` expected an argument
of type ``int`` but instead got an unevaluated computation.

Erased values are for specification and proof only
..................................................

Let's take a closer look at how dereferencing works in the function
``value_of`` below:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //value_of$
   :end-before: ```

Its slightly more explicit form is shown below, where ``w:erased a``
is an erased value witnessing the current contents referenced by
``r``.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //value_of_explicit$
   :end-before: ```

Notice how the precondition requires ``pts_to r w`` while the
postcondition changes to ``pts_to r v``, along with the property that
``v == reveal w``, i.e., the type proves that if we read the reference
the value we get is equal to the logical witness provided.

The logical witness is an erased value, so one cannot directly use it
in a non-ghost computation. For example, if instead of reading the
reference, we attempt to just return ``reveal w``, the
code fails to check with the error shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //value_of_explicit_fail$
   :end-before: ```

.. code-block::

    Expected a Total computation, but got Ghost

    
Heap references
^^^^^^^^^^^^^^^


Ghost references
^^^^^^^^^^^^^^^^


.. [#] We are considering switching this convention and the Pulse
       option ``--ext 'pulse:rvalues'`` can be enabled to add implicit
       dereferencing; however, it is not yet recommended for use. 
