The approach will follow the transition rules defined in [@nieuwenhuis2006solving]. Initially, the focus
will be on implementing these rules for a SAT solver, providing a foundation for later extending the approach to SMT
solving. Once the SAT solver is implemented and verified, the scope will be expanded to include transition rules for SMT
solving and possibly one or more background theories, such as arithmetic, bit-vectors, or equivalence relations.

The implementation of the solver will be done in the Coq proof assistant, which will be used both for the development of
the solver and its formal verification. Alongside correctness, the solver will also be proven to be complete and
terminating. This ensures that the solver will always find a solution if one exists (completeness) and will not enter
infinite loops (termination).

The aim is to produce a verified SMT solver where every result is provably correct, with strong guarantees of
soundness, completeness and termination.