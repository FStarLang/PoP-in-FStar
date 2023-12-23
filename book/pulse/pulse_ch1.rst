.. _Pulse_ByExample:

Pulse Basics
============

A Pulse program is embedded in an F* program, where the Pulse parts
are delimited by a syntax extension marker "\`\`\`pulse ... \`\`\`", as
shown in the program below.

.. literalinclude:: ../code/pulse/PulseByExample.fst
   :language: pulse
   :start-after: //SNIPPET_START: five
   :end-before: //SNIPPET_END

This program starts with a bit of regular F* defining ``fstar_five``
followed by an a Pulse function ``five`` that references that F*
definition and proves that it always returns the constant
``5``. Finally, we have a bit of regular F* referencing the ``five``
defined in Pulse. This is a really simple program, but it already
illustrates how Pulse and F* interact in both directions.

In what follows, unless we really want to emphasize that a fragment of
code is Pulse embedded in a larger F* context, when showing Pulse
code, we'll just show the Pulse part, omitting the "\`\`\`pulse
... \`\`\`" delimiters.


A Separation Logic Primer
^^^^^^^^^^^^^^^^^^^^^^^^^

Separation Logic was invented by John Reynolds, Peter O'Hearn, and
others in the late 1990s as a way to reason about imperative programs
that use shared, mutable data structures, e.g., linked lists and
graphs---see this paper for `an introduction to separation logic
<https://www.cs.cmu.edu/~jcr/seplogic.pdf>`_. In the subsequent
decades, several innovations were added to separation logic by many
people, generalizing it beyond just sequential heap-manipulating
programs to distributed programs, concurrent programs, asynchronous
programs, etc. that manipulate abstract resources of various kinds,
including time and space, messages sent over communication channels,
etc.

Much like other Hoare Logics, which we reviewed in :ref:`an earlier
section <Part4_Floyd_Hoare>`, separation logic has two parts to
it.

First, there is a language of propositions that describe properties
about program resources, e.g., the heap. These propositions have the
type ``vprop`` in Pulse, and under the covers in the SteelCore
semantics of Pulse, ``vprop = heap -> prop``. It is useful (at least
at first) to think of a ``vprop`` as a heap property, though we will
eventually treat it more abstractly and use it to model many other
kinds of resources.

To connect ``vprop``'s to programs, separation logics also provide a
system of Hoare triples to describe the action of a program on the
heap. For example, the Hoare triple ``{ p } c { n. q }`` describes a
program ``c`` which when run in an initial heap ``h0`` satisfying ``p
h0`` (i.e., ``p`` is a precondition); ``c`` returns a value ``n``
while transforming the heap to ``h1`` satisfying ``q n h1`` (i.e.,
``q`` is a postcondition). Pulse's program logic is a
partial-correctness logic, meaning that ``c`` may also loop forever,
deadlock with other threads, etc.

Here are some common ``vprops`` (defined in ``Pulse.Lib.Pervasives``):

  * ``emp``, the trivial proposition (equivalent to ``fun h -> True``).

  * ``pure p``, heap-independent predicate ``fun h -> p``.

Let's go back to the program ``five``:

  * It is a function with a single unit argument---Pulse functions use
    the keyword ``fn``.

  * The precondition is just ``emp``, the trivial assertion in
    separation logic, i.e., ``five`` can be called in any initial
    heap.

  * The return value is an integer ``n:int``

  * The postcondition may refer to the name of the return value (``n``
    in this case) and here claims that the final heap satisfies the
    ``pure`` proposition, ``n == 5``.

In other words, the type signature in Pulse is a convenient way to
write the Hoare triple ``{ emp } five () { n:int. pure (n == 5) }``.

At this point you may wonder if the postcondition of ``five`` is
actually strong enough. We've only said that the return value ``n ==
5`` but have not said anything about the heap that results from
calling ``five ()``. Perhaps this specification allows ``five`` to
arbitrarily change any reference in the heap, since ``pure (5 == 5)``
is true of any heap. [#]_ If you're familiar with Low*, Dafny, or
other languages based on Hoare logic for heaps, you may be wondering
about how come we haven't specified a ``modifies``-clause, describing
exactly which part of the heap a function may have changed. The nice
thing in separation logic is that there is no need to describe what
parts of the heap you may have modified. This is because a central
idea in logic is the concept of *ownership*. To a first approximation,
a computation can only access those resources that it is explicitly
granted access to in its precondition or those that it creates
itself. [#]_ In this case, with a precondition of ``emp``, the
function ``five`` does not have permission to access *any* resources,
and so ``five`` simply cannot modify the heap in any observable way.

Let's go back to ``incr`` and ``par_incr`` that we saw in the previous
section and look at their types closely. We'll need to introduce two
more common ``vprop``'s, starting with the "points-to" predicate:

  * ``pts_to x v`` asserts that the reference ``x`` points to a cell
    in the current heap that holds the value ``v``.

``vprop``'s can also be combined in various ways, the most common one
being the "separating conjunction" or ``**``.
    
  * ``p ** q``, means that the heap can be split into two *disjoint*
    fragments satisfying ``p`` and ``q``, respectively. Alternatively,
    one could read ``p ** q`` as meaning that one holds the
    permissions associated with both ``p`` and ``q`` separately in a
    given heap.

Now, perhaps the defining characteristic of separation logic is how
the ``**`` operator works in the program logic, via a key rule known
as the *frame* rule. The rule says that if you can prove the Hoare
triple ``{ p } c { n. q }``, then, for any other ``f : vprop``, you
can also prove ``{ p ** f } c { n. q ** f }``---``f`` is often called
the "frame". It might take some time to appreciate, but the frame rule
captures the essence of local, modular reasoning. Roughly, it states
that if a program is correct when it only has permission ``p`` on the
input heap, then it remains correct when run in a larger heap and is
guaranteed to preserve any property (``f``) on the part of the heap
that it doesn't touch.

With this in mind, let's look again at the type of ``incr``, which
requires permission only to ``x`` and increments it:

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //incr
   :end-before: ```

A point about the notation: The variable ``'i`` is an implicitly bound
logical variable, representing the value held in the ref-cell ``x`` in
the initial state. In this case, ``'i`` has type ``FStar.Ghost.erased
int``---we learned about :ref:`erased types in a previous section
<Part4_Ghost>`. One can also bind logical variables explicitly, e.g.,
this is equivalent:

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //incr_explicit_i
   :end-before: ```
                
Because of the frame rule, we can also call ``incr`` in a context like
``incr_frame`` below, and we can prove without any additional work
that ``y`` is unchanged.
                
.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //incr_frame
   :end-before: ```

In fact, Pulse lets use the frame rule with any ``f:vprop``, and we
get, for free, that ``incr x`` does not disturb ``f``.
      
.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //incr_frame_any
   :end-before: ```

.. [#] For experts, Pulse's separation logic is  *affine*.
       
.. [#] When we get to things like invariants and locks, we'll see how
       permissions can be acquired by other means.
