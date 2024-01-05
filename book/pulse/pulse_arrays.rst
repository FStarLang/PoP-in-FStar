.. _Pulse_Arrays:

Mutable Arrays
===============

In this chapter, we will learn about mutable arrays in Pulse. An array
is a contiguous collection of values of same type. Similar to ``ref``,
arrays in Pulse can be allocated in the stack frame of the current function
or in the heap---while the stack allocated arrays are reclaimed automatically
(e.g., when the function returns), heap allocated arrays are explicitly managed
by the program.

Pulse provides two array types: ``Pulse.Lib.Array.array t`` as the basic array type
and ``Pulse.Lib.Vec.vec t`` for heap allocated arrays. To provide code reuse, functions
that may operate over both stack and heap allocated arrays can be written using
``Pulse.Lib.Array.array t``---the ``Pulse.Lib.Vec`` library provides back-and-forth coercions
between ``vec t`` and ``array t``.

``array t``
^^^^^^^^^^^^

We illustrate the basics of ``array t`` with the help of the following example
that reads an array:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: ```pulse //readi$
   :end-before: ```

The library provides a points-to predicate ``pts_to arr s`` with the interpretation that
in the current memory, the contents of ``arr`` are same as the (functional) sequence ``s``
(``s:FStar.Seq.seq t``). Arrays can be read and written-to using indexes of type ``FStar.SizeT.t``,
a model of C ``size_t`` in F*, provided that the index is within the array bounds.

Since the representation sequence is specificational, the ``s`` argument to ``read``
is erased. Further, the refinement ``SZ.v i < Seq.length s`` enforces that the index
is in bounds. The function returns the ``i``-th element of the array, the
asserted by the postcondition vprop ``pure (x == Seq.index s (SZ.v i))``. The body
of the function uses the array read operator ``arr.(i)``.

As another example, let's write to the ``i``-th element of an array:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: ```pulse //writei$
   :end-before: ```

The function uses the array write operator ``arr(i) <- x`` and the postcondition
asserts that in the state when the function returns, the contents of the array
are same as the sequence ``s`` updated at the index ``i``.

The ``pts_to`` assertion supports fractional permissions, similar to the points-to
assertion for references. So far we have been writing ``pts_to arr s``, which is
a shorthand for ``pts_to #a arr #full_perm s``, i.e. exclusive read/write permission
on the array. While any permission suffices for reading, writing requires ``full_perm``.
For example, implementing ``write_i`` without ``full_perm`` will not work:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //writeipbegin$
   :end-before: //writeipend$

The library contains ``share`` and ``gather`` functions, similar to those for references,
to divide and combine permissions on arrays.

We now look at a couple of examples that use arrays with conditionals, loops, existentials,
and invariants, tying up all the Pulse constructs we have seen so far.

Compare
........

Let's implement a function that compares two arrays for equality:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //comparesigbegin$
   :end-before: //comparesigend$

The function takes two arrays ``a1`` and ``a2`` as input, and returns a boolean.
The postcondition ``pure (res <==> Seq.equal 's1 's2)``
specifies that the boolean is true if and only if the sequence representations of the
two arrays are equal. Since the function only reads the arrays, it is parametric in the
permissions ``p1`` and ``p2`` on the two arrays. Note that the type parameter ``t`` has
type :ref:`eqtype<Part1_equality>`, requiring that values of type ``t`` support
decidable equality.

One way to implement ``compare`` is to use a ``while`` loop, reading the two arrays
using a mutable counter and checking that the corresponding elements are equal.

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //compareimplbegin$
   :end-before: //compareimplend$

The loop invariant states that (a) the arrays are pointwise equal up to the current value
of the counter, and (b) the boolean ``b`` is true if and only if the current value
of the counter is less than the length of the arrays and the arrays are equal at that index.
While (a) helps proving the final postcondition of ``compare``, (b) is required to maintain the
invariant after the counter is incremented in the loop body.

Copy
.....

As our next example, let's implement a ``copy`` function that copies the contents
of the array ``a2`` to ``a1``.

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //copy$
   :end-before: ```

The loop invariant existentially abstracts over the contents of ``a1``, and maintains
that upto the current loop counter, the contents of the two arrays are equal. Rest of
the code is straightforward, the loop conditional checks that the loop counter is less
than the array lengths and the loop body copies one element at a time.

The reader will notice that the postcondition of ``copy`` is a little convoluted.
A better signature would be the following, where we directly state that the
contents of ``a1`` are same as ``'s2``:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //copy2sigbegin$
   :end-before: //copy2sigend$

We can implement this signature, but it requires one step of rewriting at the end
after the ``while`` loop to get the postcondition in this exact shape:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //copy2rewriting$
   :end-before: //copy2rewritingend$

A ``rewrite`` explicits rewrites a context vprop; Pulse checker checks that the
rewriting is sound. We will learn about ``rewrite`` in later chapters.


Stack allocated arrays
^^^^^^^^^^^^^^^^^^^^^^^

Stack arrays can be allocated using the expression ``[| v; n |]``. It allocates
an array of size ``n``, with all the array elements initialized to ``v``.
It provides the postcondition that the newly create array points to a length ``n``
sequence of ``v``. The following example allocates two arrays on the stack and
compares them using the ``compare`` function above.

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: ```pulse //compare_stack_arrays$
   :end-before: ```

As with the stack references, stack arrays don't need to be deallocated or
dropped, they are reclaimed automatically when the function returns. As a result,
returning them from the function is not allowed:

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //ret_stack_array$
   :end-before: //ret_stack_array_end$

Heap allocated arrays
^^^^^^^^^^^^^^^^^^^^^^

Pulse library ``Pulse.Lib.Vec`` provides the heap allocated array type ``vec t``.
Similar to ``array``, ``vec`` is accompanied with a ``pts_to`` assertion with support
for fractional permissions, ``share`` and ``gather`` for dividing and combining permissions,
and read and write functions. However, unlike ``array``, the ``Vec`` library provides allocation
and free functions.

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: //heaparray$
   :end-before: //heaparrayend$

As with the heap references, heap allocated arrays can be coerced to ``array`` using the coercion
``vec_to_array``. To use the coercion, it is often required to convert ``Vec.pts_to`` to ``Array.pts_to``
back-and-forth; the library provides ``to_array_pts_to`` and ``to_vec_pts_to`` lemmas for this purpose.

The following example illustrates the pattern. It copies the contents of a stack array into a heap array,
using the ``copy2`` function we wrote above.

.. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
   :language: pulse
   :start-after: ```pulse //copyuse$
   :end-before: ```

Note how the assertion for ``v`` transforms from ``V.pts_to`` to ``pts_to`` (the points-to assertion
for arrays) and back. It means that array algorithms and routines can be implemented with the
``array t`` type, and then can be reused for both stack- and heap-allocated arrays.

Finally, though the name ``vec a`` evokes the Rust ``std::Vec`` library, we don't yet support automatic
resizing.
