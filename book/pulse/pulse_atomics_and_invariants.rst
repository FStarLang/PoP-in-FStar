.. _Pulse_atomics_and_invariants:

Atomic Operations and Invariants
================================

In this section, we finally come to some concurrency related
constructs.

Concurrency in Pulse is built around two concepts:

  * **Atomic operations**: operations that are guaranteed to be
    executed in a single-step of computation without interruption by
    other threads.

  * **Invariants**: named predicates that are enforced to be true at
    all times.  Atomic operations can make use of invariants, assuming
    they are true in the current state, and enforced to be true again
    once the atomic step concludes.

Based on this, and in conjunction with all the other separation logic
constructs that we've learned about so far, notably the use of ghost
state, Pulse enables proofs of concurrent programs.

Atomic Operations
.................

We've learned so far about :ref:`two kinds of Pulse computations
<Pulse_higher_order>`:

  * General purpose, partially correct computations, with the ``stt``
    computation type

  * Ghost computations, proven totally correct, and enforced to be
    computatationally irrelevant with the ``stt_ghost`` computation
    type.

Pulse offers a third kind of computation, *atomic* computations, with
the ``stt_atomic`` computation type. Here is the signature of
``read_atomic`` and ``write_atomic`` from ``Pulse.Lib.Reference``:

.. code-block:: pulse

   atomic
   fn read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
   requires pts_to r #p n
   returns x:U32.t
   ensures pts_to r #p n ** pure (reveal n == x)

.. code-block:: pulse   

   atomic
   fn write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
   requires pts_to r n
   ensures pts_to r x

The ``atomic`` annotation on these functions claims that reading and
writing 32-bit integers can be done in a single atomic step of
computation.

This is an assumption about the target architecture on which a Pulse
program is executed. It may be that on some machines, 32-bit values
cannot be read or written atomically. So, when using atomic
operations, you should be careful to check that its safe to assume
that these operations truly are atomic.

Pulse also provides a way for you to declare that other operations are
atomic, e.g., maybe your machine supports 64-bit or 128-bit atomic
operations---you can program the semantics of these operations in F*
and add them to Pulse, marking them as atomic.

Sometimes, particularly at higher order, you will see atomic
computations described by the computation type below:

.. code-block:: fstar

   val stt_atomic (t:Type) (i:inames) (pre:vprop) (post:t -> vprop)
     : Type u#2

Like ``stt_ghost``, atomic computations are total and live in universe
``u#2``. As such, you cannot store an atomic function in the state,
i.e., ``ref (unit -> stt_atomic t i p q)`` is not a well-formed type.

Sometimes, we will also refer to the following computation type:

.. code-block:: fstar

   val stt_unobservable (t:Type) (i:inames) (pre:vprop) (post:t -> vprop)
     : Type u#2

Unobservable computations, or ``stt_unobservable``, are very closed
related to ghost computations, though are slightly different
technically---we'll learn more about these shortly.

Atomic computations are also indexed by ``i:inames``, where ``inames``
is a set of invariant names. We'll learn about these next.

Invariants
..........

In ``Pulse.Lib.Core``, we have the following types:

.. code-block:: fstar

   val inv (p:vprop) : Type u#0
   val iname : eqtype
   val name_of_inv #p (i:inv p) : GTot iname

The type ``inv p`` is the type of an *invariant*. Think of ``i:inv p``
as a *token* which guarantees that ``p`` is true in the current state
and all future states of the program. Every invariant has a name,
``name_of_inv i``, though, the name is only relevant in
specifications, i.e., it is ghost.
   
Creating an invariant
+++++++++++++++++++++

Let's start by looking at how to create an invariant.

First, let's define a regular ``vprop``, ``owns x``, to mean that we
hold full-permission on ``x``.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: fstar
   :start-after: //owns$
   :end-before: //owns$

Now, if we can currently proves ``pts_to r x`` then we can turn it
into an invariant ``i:inv (owns r)``, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //create_invariant$
   :end-before: ```

Importantly, when we turn ``pts_to r x`` into ``inv (owns r)``, **we
lose** ownership of ``pts_to r x``. Remember, once we have ``inv (owns
r)``, Pulse's logic aims to that ``owns r`` remains true always. If we
were allowed to retain ``pts_to r x``, while also creating an ``inv
(owns r)``, we can clearly break the invariant, e.g., by freeing
``r``.

.. note::

   A tip: When using an ``inv p``, it's a good idea to make sure that
   ``p`` is a user-defined predicate. For example, one might think to
   just write ``inv (exists* v. pts_to x v)`` instead of defining an
   auxiliary predicate for ``inv (owns r)``. However, the some of the
   proof obligations produced by the Pulse checker are harder for the
   SMT solver to prove if you don't use the auxiliary predicate and
   you may start to see odd failures. This is something we're working
   to improve. In the meantime, use an auxiliary predicate.

``new_invariant`` is unobservable
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The type of ``new_invariant`` is shown below:

.. code-block:: fstar

   val new_invariant (p:vprop)
   : stt_unobservable (inv p) emp_inames p (fun _ -> emp)

The ``stt_unobservable`` says that ``new_invariant`` is an atomic step
of computation from Pulse's perspective, but it doesn't read or change
any observable state. In that regard, ``stt_unobservable`` is a lot
like ``stt_ghost``; however, while ``stt_ghost`` computations are
allowed to use F* ghost operations like ``reveal : erased a -> GTot
a``, unobservable computations are not.

A ``stt_ghost`` computation with a non-informative result can be
lifted to ``stt_unobservable``.

Opening an invariant
++++++++++++++++++++

Now that we've allocated an ``inv (owns r)``, what can we do with it?
As we said earlier, one can make use of the ``owns r`` in an atomic
computation, so long as we restore it at the end of the atomic
step.

The ``with_invariants`` construct gives us access to the invariant
within the scope of at most one atomic step, preceded or succeeded by
as many ghost or unobservable steps as needed.

The general form of ``with_invariants`` is as follows, to "open"
invariants ``i_1`` to ``i_k`` in the scope of ``e``.

.. code-block:: pulse

   with_invariants i_1 ... i_k
   returns x:t
   ensures post
   { e }


In many cases, the ``returns`` and ``ensures`` annotations are
omitted, since it can be inferred.
   
This is syntactic sugar for the following nest:

.. code-block:: pulse

   with_invariants i_1 {
    ...
     with_invariants i_k
     returns x:t
     ensures post
     { e }
    ...
   }

Here's the rule for opening a single invariant ``i:inv p`` using
``with_invariant i { e }`` is as follows:

* ``i`` must have type ``inv p``, for some ``p:vprop``   
   
* ``e`` must have the type ``stt_atomic t j (p ** r) (fun x -> p ** s
  x)``. [#]_ That is, ``e`` requires and restores the invariant ``p``,
  while also transforming ``r`` to ``s x``, all in at most one atomic
  step. Further, the ``name_of_inv i`` must not be in the set ``j``.

* ``with_invariants i { e }`` has typ ``stt_atomic t (add_inv i j) r
  s``. That is, ``e`` gets to use ``p`` for a step, and from the
  caller's perspective, the context was transformed from ``r`` to
  ``s``, while the use of ``p`` is hidden.

* Pay attention to the ``add_inv i j`` index on ``with_invariants``:
  ``stt_atomic`` (or ``stt_unobservable``) computation is indexed by
  the names of all the invariants that it may open.

Let's look at a few examples to see how ``with_invariants`` works.

.. [#]

   Note, ``e`` may also have type ``stt_unobservable t j (p ** r) (fun
   x -> p ** s x)``, in which case ``with_invariant i { e }`` has type
   ``stt_unobservable t (add_inv i j) r s``.

    
Updating a reference
~~~~~~~~~~~~~~~~~~~~

In the example below, given ``inv (owns r)``, we can atomically update
a reference with a pre- and postcondition of ``emp``.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_atomic$
   :end-before: ```

* At the start of the ``with_invariants`` scope, we have ``owns r`` in
  the context.

* The ghost step ``unfold owns`` unfolds it to its definition.

* Then, we do a single atomic action, ``write_atomic``. 

* And follow it up with a ``fold owns``, another ghost step.

* The block within ``with_invariants i`` has type ``stt_atomic unit
  emp_inames (owns r ** emp) (fun _ -> owns r ** emp)``

* Since we opened the invariant ``i``, the type of
  ``update_ref_atomic`` records this in the ``opens (singleton i)``
  annotation; equivalently, the type is ``stt_atomic unit
  (singleton i) emp (fun _ -> emp)``. When the ``opens`` annotation is
  omitted, it defaults to ``emp_inames``, the empty set of invariant
  names.

Double opening is unsound
~~~~~~~~~~~~~~~~~~~~~~~~~

To see why we have to track the names of the opened invariants,
consider the example below. If we opened the same invariant twice
within the same scope, then it's easy to prove ``False``:

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //double_open_bad$
   :end-before: //double_open_bad$

Here, we open the invariants ``i`` twice and get ``owns r ** owns r``,
or more than full permission to ``r``---from this, it is easy to build
a contradiction.


Subsuming atomic computations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Atomic computations can be silently converted to regular, ``stt``
computations, while forgetting which invariants they opened. For
example, ``update_ref`` below is not marked atomic, so its type
doesn't record which invariants were opened internally.
  
.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref$
   :end-before: ```

This is okay, since a non-atomic computation can never appear within a
``with_invariants`` block---so, there's no fear of an ``stt``
computation causing an unsound double opening. Attempting to use a
non-atomic computation in a ``with_invariants`` block produces an
error, as shown below.


.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_fail$
   :end-before: //update_ref_fail$

.. code-block::

   - This computation is not atomic nor ghost. `with_invariants`
     blocks can only contain atomic computations.
