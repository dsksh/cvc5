Real-Blasting FPA Theory Solver
=========================

The real-blasting theory solver provides an alternative method for reasoning about formulas in the floating-point arithmetic.
The solver is implemented as an extended solver of nonlinear real-integer arithmetic (``NLRIA``) theory solver.
Internally, it performs term translation from FPA to RIA and relies on the RIA solver for the basic solving process.

Currently, the solver supports a subset of the quantifier-free fragment of an FPA theory (``QF_FP``).
Most operators are supported, but some e.g. ``fp.fma``, ``fp.sqrt`` and ``to_sbv`` are not supported.

The solver is enabled (and replaces the default FPA solver) by giving an option ``--fp-to-real`` on the command line.

Options
+++++++

``--fp-to-real`` [type ``bool``]: 

Enable the real-blasting theory solver.

``--fp2real-ll`` [``weak | mid | strong``, default ``mid``]:

Set the degree of lazy learning, which instantiates the axioms for each FPA efficiently based on the solving context. With ``weak``, the axioms are instantiated more eagerly instead of begin delayed.

``--fp2real-vr`` [``limited | mid | all``, default ``mid``]:

Set whether to limit learning the value-refine lemmas, which are lemmas per FPA operation based on concrete assignments to the argument(s). With ``all``, the number may increase.
