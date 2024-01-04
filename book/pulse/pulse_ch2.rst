.. _Pulse_References:

Mutable References
==================

Pulse aims to support programming with explicit control over memory
management and without need for a garbage collector, similar to
languages like C or Rust, but, of course, in a proof-oriented style.
Towards that end, one of the main features it offers (especially in
comparison to purely functional F*) is support for references to
mutable memory that can be both allocated and reclaimed.

In this chapter, we'll learn about three kinds of mutable references:
stack references, heap references (or boxes), and ghost
references. Stack references point to memory allocated in the stack
frame of the current function (in which case the memory is reclaimed
when the function returns). Heap references, or boxes, point to memory
locations in the heap, and heap memory is explicitly reclaimed by
calling ``drop`` or ``free``. Ghost references are for specification
and proof purposes only and point to memory locations that do not
really exist at runtime.

``ref t``: Stack or Heap References
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Most of the operations on mutable references are agnostic to whether
the memory referenced resides on the stack or the heap---the main
difference is that stack references are allocated in a scope and
implicitly reclaimed when they go out of scope; whereas heap
references are explicitly allocated and deallocated.

The type ``Pulse.Lib.Reference.ref t`` is the basic type of a mutable
reference. We have already seen ``ref t`` used in the ``incr``
function of the previous section. We show below another common
function to swap the contents of two references:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //swap$
   :end-before: ```

Reading a reference
...................


Let's start by taking a closer look at how dereferencing works in the
function ``value_of`` below:

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


Erased values are for specification and proof only
..................................................

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

Writing through a reference
...........................

The function ``assign`` below shows how to mutate the contents of a
reference---the specification shows that when the function returns,
``r`` points to the assigned value ``v``.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //assign$
   :end-before: ```
                    
                
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
   :start-after: ```pulse //add$
   :end-before: ```

Meanwhile, the function ``quadruple`` calls ``add`` twice to double
the value stored in ``r`` each time.
                
.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //quadruple$
   :end-before: ```

The comments show how the proof state evolves after each command. A
few points to note about the Pulse checker:

  * Pulse typechecks each step of a program by checking the current
    assumptions in the proof state are sufficient to prove the
    precondition of that step, ensuring that all unused permissions
    are retained in the context---using the frame rule, discussed in
    the previous section

  * Like F*, Pulse tries to instantiate implicit arguments
    automatically, e.g., at the second call to ``add``, Pulse
    automatically instantiates ``'v`` to ``v2``.

  * Pulse proves ``pure`` properties automatically, by sending queries
    to the SMT solver.

  * Pulse also uses the SMT solver to convert ``pts_to r (v2 + v2)``
    to ``pts_to r (4 * 'v)``.

  * Pulse simplifies ``vprops`` implicitly, e.g., Pulse will
    automatically rewrite ``emp ** p`` to ``p``.

Stateful commands are explicitly sequenced
..........................................

Pulse expects the results of all stateful operations to be explicitly
``let``-bound. For example, the following code fails to type checked:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //quad FAIL$
   :end-before: ```
               

.. code-block::

  - Expected type "int"; but "!r" has type
    "stt int
         (pts_to r (reveal (*?u93*) _))
         (fun x -> pts_to r x ** pure (reveal (*?u93*) _ == x))"

The error points to the first occurrence of ``(!r)``. The message is
admittedly cryptic and should be improved. As we'll see in a later
chapter, the type ``stt _ _ _`` is the type of an unevaluated Pulse
comptuation---this error complains that ``add`` expected an argument
of type ``int`` but instead got an unevaluated computation.

Fractional Permissions
......................

Pulse distinguishes read-only references from read/write
references. As in languages like Rust, Pulse ensures that there can be
at most one thread that holds read/write permission to a reference,
although many threads can share read-only references. This ensures
that Pulse programs are free of data races. At a more abstract level,
Pulse's permission system ensures that one can reason locally about
the contents of memory, since if one holds read/write permission to a
reference, one can be sure that its contents cannot be changed by some
part of the program.

To implement this permission discipline, Pulse uses a system of
fractional permissions, an idea due to `John Boyland
<https://link.springer.com/chapter/10.1007/3-540-44898-5_4>`_.  In
particular, the ``pts_to`` predicate that we have been using actually
has an additional implicit arguments that describes how much
permission one holds on a reference.

The full type of the ``pts_to`` predicate is shown below:

.. code-block:: fstar

   val pts_to (#a:Type u#0) (r:ref a) (#p:perm) (v:a) : vprop

We have so far been writing ``pts_to r v`` instead of ``pts_to #a r #p
v``. Usually, one does not need to write the first argument ``#a``
since it is computed by type inference; the ``#p:perm`` argument is
more interesting---when omitted, it defaults to the value
``full_perm``. The type ``perm`` (defined in
``Steel.FractionalPermission``) is a real number strictly greater than
``0`` and less than or equal to ``1``, where ``1`` is written
``full_perm``.

The ``pts_to r #full_perm v`` represents exclusive, read/write
permission on a reference. Revisiting the ``assign`` function from
previously, we can write down the permissions explicitly.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //assign_full_perm$
   :end-before: ```
   
In contrast, when reading a reference, any permission ``p`` will do,
as shown below:

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //value_of_perm$
   :end-before: ```

If we try to write to a reference without holding full permission on
it, Pulse rejects the program, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: //assign_perm FAIL$
   :end-before: //end assign_perm FAIL$

.. code-block:: fstar

  - Cannot prove:
      pts_to #a r #full_perm (reveal #a _)
  - In the context:
      pts_to #a r #p (reveal #a w)   

The full error message requires the F* option ``--print_implicits``.

The functions ``share`` and ``gather`` allow one to divide and combine
permissions on references, as shown below.


.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //share_ref$
   :end-before: ```

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: ```pulse //gather_ref$
   :end-before: ```

    
Stack references
^^^^^^^^^^^^^^^^


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

.. code-block:: fstar

  - Cannot prove:
      pts_to s 0
  - In the context:
      emp

    
Heap references
^^^^^^^^^^^^^^^

The type ``Pulse.Lib.Box.box t`` is the type of heap references---the
name is meant to evoke Rust's type of heap references, ``Box<T>``. We
use the module alias ``Box`` in what follows:

.. code-block:: fstar

   module Box = Pulse.Lib.Box

The ``Box`` module provides most of the same predicates and functions
that we have with regular references, including ``pts_to``, ``(!)``,
``(:=)``, ``share``, and ``gather``. Additionally, heap references are
explicitly allocated using ``alloc`` and deallocated using ``free``,
as shown below. 

.. literalinclude:: ../code/pulse/PulseTutorial.Box.fst
   :language: pulse
   :start-after: ```pulse //new_heap_ref$
   :end-before: ```
                
Note, we can return a freshly allocated heap reference from a
function, unlike a ``let mut`` scoped, stack-allocated reference.

In the following example, we use ``open Box;`` to open the namespace
``Box`` in the following scope.

.. literalinclude:: ../code/pulse/PulseTutorial.Box.fst
   :language: pulse
   :start-after: ```pulse //last_value_of$
   :end-before: ```

``box t`` references can be demoted to regular ``ref t`` references
for code reuse. For example, in the code below, we increment the
contents of ``r:box int`` by first calling ``Box.to_ref_pts_to`` to
convert ``Box.pts_to r 'v`` to a regular ``pts_to (box_to_ref r) 'v``;
then calling ``incr (box_to_ref r)``; and then converting back to a
``Box.pts_to``.

.. literalinclude:: ../code/pulse/PulseTutorial.Box.fst
   :language: pulse
   :start-after: ```pulse //incr_box$
   :end-before: ```

Finally, unlike Rust's ``Box<T>`` type, which is always treated
linearly (i.e., in Rust, one always holds exclusive read/write
permission on a ` ``Box<T>``), in Pulse, ``Box.pts_to r #p v`` has an
implicit fractional permission as with regular references.

Ghost references
^^^^^^^^^^^^^^^^


.. [#] We are considering switching this convention and the Pulse
       option ``--ext 'pulse:rvalues'`` can be enabled to add implicit
       dereferencing; however, it is not yet recommended for use. 
