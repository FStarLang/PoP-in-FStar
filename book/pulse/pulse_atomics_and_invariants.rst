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
    computationally irrelevant with the ``stt_ghost`` computation
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
     : Type u#4

Like ``stt_ghost``, atomic computations are total and live in universe
``u#4``. As such, you cannot store an atomic function in the state,
i.e., ``ref (unit -> stt_atomic t i p q)`` is not a well-formed type.

Atomic computations and ghost computations are also indexed by
``i:inames``, where ``inames`` is a set of invariant names. We'll
learn about these next.

Invariants
..........

In ``Pulse.Lib.Core``, we have the following types:

.. code-block:: fstar

   [@@erasable]
   val iref : Type0
   val inv (i:iref) (p:vprop) : vprop

Think of ``inv i p`` as a predicate asserting that ``p`` is true in
the current state and all future states of the program. Every
invariant has a name, ``i:iref``, though, the name is only relevant in
specifications, i.e., it is erasable.

A closely related type is ``iname``:

.. code-block:: fstar

   val iname : eqtype
   let inames = erased (FStar.Set.set iname)

Every ``iref`` can be turned into an ``iname``, with the function
``iname_of (i:iref): GTot iname``.

Invariants are duplicable, i.e., from ``inv i p`` one can prove ``inv
i p ** inv i p``, as shown by type of ``Pulse.Lib.Core.dup_inv``
below:

.. code-block:: fstar
		    
    val dup_inv (i:iref) (p:vprop)
      : stt_ghost unit emp_inames (inv i p) (fun _ -> inv i p ** inv i p)


Boxable predicates
++++++++++++++++++

Pulse's language of predicates, i.e., the type ``vprop``, is
stratified. The type ``boxable`` is a refinement of ``vprop``, defined
as shown below in ``Pulse.Lib.Core``

.. code-block:: fstar

   let boxable = v:vprop { is_big v }

That is, certain ``vprops``, i.e., those that satisfy ``is_big``, are
``boxable`` predicates. All the predicates that we have encountered so
far are boxable, except for the ``inv i p`` predicate. For example,
``pts_to x v`` is boxable; ``exists* x. p x`` is boxable if ``p x`` is
boxable; etc. However ``inv i p`` is not boxable.

Why does this matter? It turns out that PulseCore, the logic on which
Pulse is built, only allows turning boxable predicates into
invariants. That is, while one can build an invariant such as ``inv i
(exists* v. pts_to x v)``, one **cannot** nest invariants, i.e., there
is no meaningful way to construct an instance of ``inv i (inv j p)``.

This restriction is a fundamental limitation of PulseCore: invariants
cannot mention other invariants. In more technical terms, *invariants
are predicative*. One might wonder whether this limitation is
significant: after all, why might one want to construct an invariant
that states that some ``p`` is already an invariant? It turns out that
such predicates, although not very common, are useful and the
inability to nest invariants in Pulse makes some styles of proofs
awkward or perhaps even impossible. Nevertheless, forcing invariants
to be predicative gives Pulse a simple foundational model in PulseCore
in terms of a standard, predicative, dependently typed logic.

Let's look next at how to turn a boxable predicate into an invariant.

Creating an invariant and boxable predicates
++++++++++++++++++++++++++++++++++++++++++++

Let's start by looking at how to create an invariant.

First, let's define a predicate ``owns x``, to mean that we hold
full-permission on ``x``.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: fstar
   :start-after: //owns$
   :end-before: //end owns$

Notice the type annotation on ``owns`` claims that it is ``boxable``,
and indeed F*'s refinement type checker automatically proves that it
is.

Now, if we can currently prove ``pts_to r x`` then we can turn it into
an invariant ``inv i (owns r)``, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //create_invariant$
   :end-before: //end create_invariant$

Importantly, when we turn ``pts_to r x`` into ``inv i (owns r)``, **we
lose** ownership of ``pts_to r x``. Remember, once we have ``inv i
(owns r)``, Pulse's logic aims to prove that ``owns r`` remains true
always. If we were allowed to retain ``pts_to r x``, while also
creating an ``inv i (owns r)``, we can clearly break the invariant,
e.g., by freeing ``r``.

.. note::

   A tip: When using an ``inv i p``, it's a good idea to make sure
   that ``p`` is a user-defined predicate. For example, one might
   think to just write ``inv i (exists* v. pts_to x v)`` instead of
   defining an auxiliary predicate for ``inv i (owns r)``. However, the
   some of the proof obligations produced by the Pulse checker are
   harder for the SMT solver to prove if you don't use the auxiliary
   predicate and you may start to see odd failures. This is something
   we're working to improve. In the meantime, use an auxiliary
   predicate.

Note, if one were to try to allocate an invariant for a non-boxable predicate,
typechecking fails, as shown in the example below:

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //create_non_boxable$
   :end-before: //end create_non_boxable$

failing with an error pointing to the source location of the
refinement precondition, ``is_big``, at the call to ``new_invariant``.

.. code-block::

   - Assertion failed
   - The SMT solver could not prove the query. Use --query_stats for more details.
   - See also ../../../lib/pulse/lib/Pulse.Lib.Core.fsti(536,29-536,37)

As you can see, although the language does not prevent you from
writing ``inv i p`` for any predicate ``p``, the only way to allocate
an instance of ``inv i p`` is by provable that ``p`` is
``boxable``. This design is convenient since the onus of proving that
a predicate is boxable is only placed at the allocation site of the
invariant---uses of invariants do not need to worry about the
distinction between ``boxable`` and general ``vprops``.

Opening an invariant
++++++++++++++++++++

Now that we've allocated an ``inv i (owns r)``, what can we do with it?
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

Here's the rule for opening a single invariant ``inv i p`` using
``with_invariant i { e }`` is as follows:

* ``i`` must have type ``iref`` and ``inv i p`` must be provable in
  the current context, for some ``p:vprop``
   
* ``e`` must have the type ``stt_atomic t j (p ** r) (fun x -> p ** s
  x)``. [#]_ That is, ``e`` requires and restores the invariant ``p``,
  while also transforming ``r`` to ``s x``, all in at most one atomic
  step. Further, the ``name_of_inv i`` must not be in the set ``j``.

* ``with_invariants i { e }`` has type ``stt_atomic t (add_inv i j)
  (inv i p ** r) (fun x -> inv i p ** s x)``. That is, ``e`` gets to
  use ``p`` for a step, and from the caller's perspective, the context
  was transformed from ``r`` to ``s``, while the use of ``p`` is
  hidden.

* Pay attention to the ``add_inv i j`` index on ``with_invariants``:
  ``stt_atomic`` (or ``stt_ghost``) computation is indexed by
  the names of all the invariants that it may open.


Let's look at a few examples to see how ``with_invariants`` works.

.. [#]

    Alternatively ``e`` may have type ``stt_ghost t j (p ** r) (fun x
    -> p ** s x)``, in which case the entire ``with_invariants i { e
    }`` block has type ``stt_ghost t (add_inv i j) (inv i p ** r) (fun
    x -> inv i p ** s x)``, i.e., one can open an invariant and use it
    in either an atomic or ghost context.
    
    
Updating a reference
~~~~~~~~~~~~~~~~~~~~

In the example below, given ``inv i (owns r)``, we can atomically
update a reference with a pre- and postcondition of ``emp``.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_atomic$
   :end-before: //end update_ref_atomic$

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
  (singleton i) (inv i (owns r)) (fun _ -> inv i (owns r))``. When the
  ``opens`` annotation is omitted, it defaults to ``emp_inames``, the
  empty set of invariant names.

Double opening is unsound
~~~~~~~~~~~~~~~~~~~~~~~~~

To see why we have to track the names of the opened invariants,
consider the example below. If we opened the same invariant twice
within the same scope, then it's easy to prove ``False``:

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //double_open_bad$
   :end-before: //end double_open_bad$

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
   :end-before: //end update_ref$

This is okay, since a non-atomic computation can never appear within a
``with_invariants`` block---so, there's no fear of an ``stt``
computation causing an unsound double opening. Attempting to use a
non-atomic computation in a ``with_invariants`` block produces an
error, as shown below.


.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_fail$
   :end-before: //end update_ref_fail$

.. code-block::

   - This computation is not atomic nor ghost. `with_invariants`
     blocks can only contain atomic computations.