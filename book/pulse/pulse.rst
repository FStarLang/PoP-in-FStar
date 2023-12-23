.. _PartPulse:

################################################################
Pulse: Proof-oriented Programming in Concurrent Separation Logic
################################################################

Many F* projects involve building domain-specific languages with
specialized programming and proving support. For example, `Vale
<https://github.com/project-everest/vale>`_ supports program proofs
for a structured assembly language; `Low*
<https://fstarlang.github.io/lowstar/html/>`_ provides effectful
programming in F* with a C-like memory model; `EverParse
<https://github.com/project-everest/everparse>`_ is a DSL for writing
low-level parsers and serializers. Recently, F* has gained new
features for building DSLs embedded in F* with customized syntax, type
checker plugins, extraction support, etc., with *Pulse* as a showcase
example of such a DSL.

Pulse is a new programming language embedded in F* and inheriting many
of its features (notably, it is higher order and has dependent types),
but with built-in support for programming with mutable state and
concurrency, with specifications and proofs in `Concurrent Separation
Logic <https://en.wikipedia.org/wiki/Separation_logic>`_.

As a first taste of Pulse, here's a function to increment a mutable
integer reference.

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //incr
   :end-before: ```

And here's a function to increment two references in parallel.

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: ```pulse //par_incr
   :end-before: ```

You may not have heard about separation logic before---but perhaps
these specifications already make intuitive sense to you. The type of
``incr`` says that if "x points to 'i" initially, then when ``incr``
returns, "x points to 'i + 1"; while ``par_incr`` increments the
contents of ``x`` and ``y`` in parallel by using the ``par``
combinator.

Concurrent separation logic is an active research area and there are
many such logics out there, all with different tradeoffs. Pulse's
logic is based on a logic called `SteelCore
<https://www.fstar-lang.org/papers/steelcore/>`_ and a prior DSL built
on top of SteelCore called `Steel
<https://www.fstar-lang.org/papers/steel/>`_. SteelCore itself builds
on ideas from `Iris <https://iris-project.org/>`_ and `Hoare Type
Theory <https://software.imdea.org/~aleks/htt/>`_. But, you should not
need to know much about any of this research--- we'll start from the
basics and explain what you need to know about concurrent separation
logic to start programming and proving in Pulse. Additionally, Pulse
is an extension of F*, so all you've learned about F*, lemmas,
dependent types, refinement types, etc. will be of use again. 

..   .. image:: pulse_arch.png

  
.. toctree::
   :maxdepth: 1
   :caption: Contents:

   pulse_ch1
