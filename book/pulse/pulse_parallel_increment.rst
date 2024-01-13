.. _Pulse_parallel_increment:

Parallel Increment
==================

In this chapter, we look at an example first studied by Susan Owicki
and David Gries, in a classic paper titled `Verifying properties of
parallel programs: an axiomatic approach
<https://dl.acm.org/doi/10.1145/360051.360224>`_. The problem involves
proving that a program that atomically increments an integer reference
``r`` twice in parallel correctly adds 2 to ``r``. There are many ways
to do this---Owicki & Gries' approach, adapted to a modern separation
logic, involves the use of additional ghost state and offers a modular
way to structure the proof.

While this is a very simple program, it captures the essence of some
of the reasoning challenges posed by concurrency: two threads interact
with a shared resource, contributing to it in an undetermined order,
and one aims to reason about the overall behavior, ideally without
resorting to directly analyzing each of the possible interleavings.

Parallel Blocks
...............

Pulse provides a few primitives for creating new threads. The most
basic one is parallel composition, as shown below:

.. code-block:: pulse

   parallel
   requires p1 and p2
   ensures q1 and q2
   { e1 }
   { e2 }

The typing rule for this construct requires:

.. code-block:: pulse

   val e1 : stt a p1 q1
   val e2 : stt b p2 q2

and the ``parallel`` block then has the type:

.. code-block:: pulse

   stt (a & b) (p1 ** p2) (fun (x, y) -> q1 x ** q2 y)

In other words, if the current context can be split into separate
parts ``p1`` and ``p2`` satisfying the preconditions of ``e1`` and
``e2``, then the parallel block executes ``e1`` and ``e2`` in
parallel, waits for both of them to finish, and if they both do,
returns their results as a pair, with their postconditions on each
component.

Using ``parallel``, one can easily program the ``par`` combinator
below:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //par$
   :end-before: ```

As we saw in the :ref:`introduction to Pulse <PartPulse>`, it's easy
to increment two separate references in parallel:

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //par_incr
   :end-before: ```

But, what if we wanted to increment the same reference in two separate
threads? That is, we wanted to program something like this:

.. code-block:: pulse

   fn add2 (x:ref int)
   requires pts_to x 'i
   ensures pts_to x ('i + 2)
   {
      par (fun _ -> incr x)
          (fun _ -> incr x)
   }

But, this program doesn't check. The problem is that we have only a
single ``pts_to x 'i``, and we can't split it to share among the
threads, since both threads require full permission to ``x`` to update
it.
   
Further, for the program to correctly add ``2`` to ``x``, each
increment operations must take place atomically, e.g., if the two
fragments below were executed in parallel, then they may both read the
initial value of ``x`` first, bind it to ```v``, and then both update
it to ``v + 1``.

.. code-block:: pulse
                
   let v = !x;      ||    let v = !x;
   x := v + 1;      ||    x := v + 1;

Worse, without any synchronization, on modern processors with weak
memory models, this program could exhibit a variety of other
behaviors.

To enforce synchronization, we could use a lock, e.g., shown below:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: ```pulse //attempt$
   :end-before: ```

This program is type correct and free from data races. But, since the
lock holds the entire permission on ``x``, there's no way to give this
function a meaningful postcondition, aside from ``emp``.

A First Take, with Locks
........................

Owicki and Gries' idea was to augment the program with axuiliary
variables, or ghost state, that are purely for specification
purposes. Each thread gets its own piece of ghost state, and accounts
for how much that thread has contributed to the current value of
shared variable. Let's see how this works in Pulse.

The main idea is captured by ``lock_inv``, the type of the predicate
protected by the lock:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: fstar
   :start-after: //lock_inv$
   :end-before: //lock_inv$

Our strawman ``lock`` in the ``attempt`` shown before had type ``lock
(exists* v. pts_to x v)``. This time, we add a conjunct that refines
the value ``v``, i.e., the predicate ``contributions l r init v`` says
that the current value of ``x`` protected by the lock (i.e., ``v``) is
equal to ``init + vl + vr``, where ``init`` is the initial value of
``x``; ``vl`` is the value of the ghost state owned by the "left"
thread; and ``vr`` is the value of the ghost state owned by the
"right" thread. In other words, the predicate ``contributions l r init
v`` shows that ``v`` always reflects the values of the contributions
made by each thread.

Note, however, the ``contributions`` predicate only holds
half-permission on the left and right ghost variables. The other half
permission is held outside the lock and allows us to keep track of
each threads contribution in our specifications.

Here's the code for the left thread, ``incr_left``:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: ```pulse //incr_left$
   :end-before: ```

* Its arguments include ``x`` and the ``lock``, but also both pieces
  of ghost state, ``left`` and ``right``, and an erased value ``i``
  for the initial value of ``x``.

* Its precondition holds half permission on the ghost reference
  ``left``

* Its postcondition returns half-permission to ``left``, but proves
  that it was incremented, i.e., the contribution of the left thread
  to the value of ``x`` increased by ``1``.

Notice that even though we only had half permission to ``left``, the
specifications says we have updated ``left``---that's because we can
get the other half permission we need by acquiring the lock.

* We acquire the lock and update increment the value stored in ``x``.

* And then we follow the increment with several ghost steps:

  - Gain full permission on ``left`` by combining the half permission
    from the precondition with the half permission gained from the
    lock.

  - Increment ``left``.

  - Share it again, returning half permission to the lock when we
    release it.

* Finally, we ``GR.pts_to left #one_half (`vl + 1)`` left over to
  return to the caller in the postcondition.

The code of the right thread is symmetrical, but in this, our first
take, we have to essentially repeat the code---we'll see how to remedy
this shortly.

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: ```pulse //incr_right$
   :end-before: ```

Finally, we can implement ``add2`` with the specification we want:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: ```pulse //add2$
   :end-before: ```

* We allocate ``left`` and ``right`` ghost references, initializing
  them to ``0``.

* Then we split them, putting half permission to both in the lock,
  retaining the other half.

* Then spawn two threads for ``incr_left`` and ``incr_right``, and get
  as a postcondition that contributions of both threads and increased
  by one each.

* Finally, we acquire the lock, get ``pts_to x v``, for some ``v``,
  and ``contributions left right i v``. Once we gather up the
  permission on ``left`` and ``right``, and now the ``contributions
  left right i v`` tells us that ``v == i + 1 + 1``, which is what we
  need to conclude.

This version also has the problem that we allocate lock and then
acquire it at the end, effectively leaking the memory associated with
the lock. We'll see how to fix that below.


Modularity with higher-order ghost code
.......................................

Our next attempt aims to write a single function ``incr``, rather than
``incr_left`` and ``incr_right``, and to give ``incr`` a more
abstract, modular specification. The style we use here is based on an
idea proposed by Bart Jacobs and Frank Piessens in a paper titled
`Expressive modular fine-grained concurrency specification
<https://dl.acm.org/doi/10.1145/1926385.1926417>`_.

The main idea is to observe that ``incr_left`` and ``incr_right`` only
deferred by the ghost code that they execute. But, Pulse is higher
order: so, why not parameterize a single function by ``incr`` and let
the caller instantiate ``incr`` twice, with different bits of ghost
code. Also, while we're at it, why not also generalize the
specification of ``incr`` so that it works with any user-chosen
abstract predicate, rather than ``contributions`` and ``left/right``
ghost state. Here's how:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: ```pulse //incr$
   :end-before: ```

As before, ``incr`` requires ``x`` and the ``lock``, but, this time,
it is parameterized by:

* A predicate ``refine``, which generalizes the ``contributions``
  predicate from before, and refines the value that ``x`` points to.

* A predicate ``aspec``, an abstract specification chosen by the
  caller, and serves as the main specification for ``incr``, which
  transitions from ``aspec 'i`` to ``aspec ('i + 1)``.

* And, finally, the ghost function itself, ``ghost_steps``, now
  specified abstractly in terms of the relationship between ``refine``,
  ``aspec`` and ``pts_to x``---it says, effectively, that once ``x``
  has been updated, the abstract predicates ``refine`` and ``aspec``
  can be updated too.

Having generalized ``incr``, we've now shifted the work to the
caller. But, ``incr``, now verified once and for all, can be used with
many different callers just by instantiating it difference. For
example, if we wanted to do a three-way parallel increment, we could
reuse our ``incr`` as is. Whereas, our first take would have to be
completely revised, since ``incr_left`` and ``incr_right`` assume that
there are only two ghost references, not three.

Here's one way to instantiate ``incr``, proving the same specification
as ``add2``.

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: ```pulse //add2_v2$
   :end-before: ```

The code is just a rearrangement of what we had before, factoring the
ghost code in ``incr_left`` and ``incr_right`` into a ghost function
``step``. When we spawn our threads, we pass in the ghost code to
either update the left or the right contribution.

This code still has two issues:

* The ghost ``step`` function is a bloated: we have essentially the
  same code and proof twice, once in each branch of the
  conditional. We can improve this by defining a custom bit of ghost
  state using Pulse's support for partial commutative monoids---but
  that's for another chapter.
  
* We still leak the memory associated with the lock at the end---we'll
  remedy that next.

Exercise
++++++++

Instead of explicitly passing a ghost function, use a quantified trade.

A version with invariants
.........................

