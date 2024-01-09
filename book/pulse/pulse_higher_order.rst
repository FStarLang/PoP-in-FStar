.. _Pulse_higher_order:

Higher Order Functions
======================

Like F*, Pulse is higher order. That is, Pulse functions are first
class and can be passed to other functions, returned as results, and
some functions can even be stored in the heap.

Pulse Computation Types
.......................

Here's perhaps the simplest higher-order function: ``apply`` abstracts
function application.

.. literalinclude:: ../code/pulse/PulseTutorial.HigherOrder.fst
   :language: pulse
   :start-after: //apply$
   :end-before: ```
                    
This function is polymorphic in the argument, result type, pre, and
post-condition of a function ``f``, which it applies to an argument
``x``. This is the first time we have written the type of a Pulse
function as an F* type. So far, we have been writing *signatures* of
Pulse functions, using the ``fn/requires/ensures`` notation, but here
we see that the type of Pulse function is of the form:

.. code-block:: pulse

   x:a -> stt b pre (fun y -> post)

where,

  * like any F* function type, Pulse functions are dependent and the
    right hand side of the arrow can mention ``x``

  * immediately to the right of the arrow is a Pulse computation type
    tag, similar to F*'s ``Tot``, or ``GTot``, etc.

  * The tag ``stt`` is the most permissive of Pulse computation type
    tags, allowing the function's body to read and write the state,
    run forever etc., but with pre-condition ``pre``, return type
    ``b``, and post-condition ``fun y -> post``.

Pulse provides several other kinds of computation types. For now, the
most important is the constructor for ghost computations. We show
below ``apply_ghost``, the analog of ``apply`` but for ``ghost``
functions.

.. literalinclude:: ../code/pulse/PulseTutorial.HigherOrder.fst
   :language: pulse
   :start-after: //apply_ghost$
   :end-before: ```

The type of ``f`` is similar to what we had before, but this time we
have:

  * compuation type tag ``stt_ghost``, indication that this function
    reads or writes ghost state only, and always terminates.

  * the return type is ``b x``

  * the next argument is ``emp_inames``, describes the set of
    invariants that a computation may open, where ``emp_inames`` means
    that this computation opens no invariants. For now, let's ignore
    this.

  * the precondition is ``pre x`` and the postcondition is ``fun y ->
    post x y``.

Counters
........

For a slightly more interesting use of higher order programming, let's
look at how to program a mutable counter. We'll start by defining the
type ``ctr`` of a counter.

.. literalinclude:: ../code/pulse/PulseTutorial.HigherOrder.fst
   :language: fstar
   :start-after: //ctr$
   :end-before: //ctr$

A counter packages the following:

  * A predicate ``inv`` on the state, where ``inv i`` states that the
    current value of the counter is ``i``, without describing exactly
    how the counter's state is implemented.

  * A stateful function ``next`` that expects the ``inv i``, returns
    the current value ``i`` of the counter, and provides ``inv (i +
    1)``.

  * A stateful function ``destroy`` to deallocate the counter.

One way to implement a ``ctr`` is to represent the state with a
heap-allocated reference. This is what ``new_counter`` does below:

.. literalinclude:: ../code/pulse/PulseTutorial.HigherOrder.fst
   :language: pulse
   :start-after: //new_counter$
   :end-before: ```

Here's how it works.

First, we allocate a new heap reference ``x`` initialized to ``0``.

Pulse allows us to define functions within any scope. So, we define
two local functions ``next`` and ``destroy``, whose implementations
and specifications are straightforward. The important bit is that they
capture the reference ``x:box int`` in their closure.

Finally, we package ``next`` and ``destroy`` into a ``c:ctr``,
instantiating ``inv`` to ``Box.pts_to x``, rewrite the context assertion
to ``c.inv 0``, and return ``c``.

In a caller's context, such as ``test_counter`` below, the fact that
the counter is implemented using a single mutable heap reference is
completely hidden.

.. literalinclude:: ../code/pulse/PulseTutorial.HigherOrder.fst
   :language: pulse
   :start-after: //test_counter$
   :end-before: ```

                

    
    

    

    
