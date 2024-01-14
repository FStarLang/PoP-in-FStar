.. _Pulse_spin_lock:

Spin Locks
==========

With atomic operations and invariants, we can build many useful
abstractions for concurrency programming. In this chapter, we'll look
at how to build a spin lock for mutual exclusion.

Representing a Lock
...................

The main idea of the implementation is to represent a lock using a
mutable machine word, where the value ``0ul`` signifies that the lock
is currently released; and ``1ul`` signifies the the lock is currently
acquired. To acquire a lock, we'll try to atomically compare-and-swap,
repeating until we succeed in setting a ``1ul`` and acquiring the
lock. Releasing the lock is simpler: we'll just set it to ``0ul``
(though we'll explore a subtlety on how to handle double releases).

From a specification perspective, a lock is lot like an invariant: the
type ``lock p`` is a kind of token that states that the lock protects
some property ``p``. Acquiring the lock provides ``p`` to the caller;
while releasing the lock requires the caller to give up ownership of
``p``. The runtime mutual exclusion is enforced by the acquire
spinning, or looping, until the lock is available. 

We'll represent a lock as a pair of reference to a ``U32.t`` and an
invariant:

.. literalinclude:: ../code/pulse/PulseTutorial.SpinLock.fst
   :language: fstar
   :start-after: //lock$
   :end-before: //lock$

The invariant states:

 * We hold full permission to the ``r:ref U32``; and

 * If ``r`` contains ``0ul``, then we also have ``p``.

Creating a lock
...............

To create a lock, we implement ``new_lock`` below. It requires the
caller to provide ``p``, ceding ownership of ``p`` to the newly
allocated ``l:lock p``

.. literalinclude:: ../code/pulse/PulseTutorial.SpinLock.fst
   :language: pulse
   :start-after: //new_lock$
   :end-before: ```

Some notes on the implementation:

* We heap allocate a reference using ``Box.alloc``, since the clearly,
  the lock has to live beyond the scope of this function's activation.

* We use ``new_invariant`` to create an ``inv (lock_inv _)``, and
  package it up with the newly allocated reference.

Acquiring a lock
................

The signature of ``acquire`` is shown below: it's says that with
``l:lock p``, we can get back ``p`` without proving anything, i.e.,
the precondition is ``emp``.

.. literalinclude:: ../code/pulse/PulseTutorial.SpinLock.fst
   :language: pulse
   :start-after: //acquire_sig$
   :end-before: //acquire_sig$

This may be seem surprising at first. But, recall that we've stashed
``p`` inside the invariant stored in the lock, and ``acquire`` is
going to keep looping until such time as a CAS on the reference in the
lock succeeds, allowing us to pull out ``p`` and return it to the
caller.

The type of a compare-and-swap is shown below, from
Pulse.Lib.Reference:

.. code-block:: fstar

   let cond b (p q:vprop) = if b then p else q

.. code-block:: pulse

   atomic
   fn cas (r:ref U32.t) (u v:U32.t) (#i:erased U32.t)
   requires pts_to r i
   returns b:bool
   ensures cond b (pts_to r v ** pure (reveal i == u)) 
                  (pts_to r i))


The specification of ``cas r u v`` says that we can try to atomically
update ``r`` from ``u`` to ``v``, and if the operation succeeds, we
learn that the initial value (``i``) of ``r`` was equal to ``u``.
                  
Using ``cas``, we can implemented ``acquire`` using a tail-recursive
function:

.. literalinclude:: ../code/pulse/PulseTutorial.SpinLock.fst
   :language: pulse
   :start-after: //acquire_body$
   :end-before: ```

The main part of the implementation is the ``with_invariants`` block.

* Its return type ``b:bool`` and postcondition is ``maybe b p``,
  signifying that after a single ``cas``, we may have ``p`` if the
  ``cas`` succeeded.

* We open ``l.i`` to get ``lock_inv``, and then try a ``cas l.r 0ul 1ul``

* If the ``cas`` succeeds, we know that the lock was initially in the
  ``0ul`` state. So, from ``lock_inv`` we have ``p``, and we can "take
  it out" of the lock and return it out of block as ``maybe true
  p``. And, importantly, we can trivially restore the ``lock_inv``,
  since we know its currently value is ``1ul``, i.e., ``maybe (1ul =
  0ul) _ == emp``.

* If the ``cas`` fails, we just restore ``lock_inv`` and return false.

Outside the ``with_invariants`` block, if the cas succeeded, then
we're done: we have ``p`` to return to the caller. Otherwise, we
recurse and try again.

Exercise
........

Rewrite the tail-recursive ``acquire`` using a while loop.

Releasing a lock
................

Releasing a lock is somewhat easier, at least for a simple version.
The signature is the dual of ``acquire``: the caller has to give up
``p`` to the lock.

.. literalinclude:: ../code/pulse/PulseTutorial.SpinLock.fst
   :language: pulse
   :start-after: //release$
   :end-before: ```

In this implementation, ``release`` unconditionally sets the reference
to ``0ul`` and reproves the ``lock_inv``, since we have ``p`` in
context.

However, if the lock was already in the released state, it may already
hold ``p``---releasing an already released lock can allow the caller
to leak resources.

Exercise
........

Rewrite ``release`` to spin until the lock is acquired, before
releasing it. This is not a particularly realistic design for avoiding
a double release, but it's a useful exercise.

Exercise
........

Redesign the lock API to prevent double releases. One way to do this
is when acquiring to lock to give out a permission to release it, and
for ``release`` to require and consume that permission.
