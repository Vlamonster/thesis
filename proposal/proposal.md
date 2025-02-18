# Master Thesis Proposal (Draft)

## Table of Contents
- [Background](#Background)
- [Research Question](#Research-question)
- [Motivation](#Motivation)
- [Approach](#Approach)
- [Expected Outcome](#Expected-outcome)
- [Related Work](#Related-work)

## Background
Satisfiability (SAT) is a fundamental problem in computer science, concerned with determining whether a given
propositional logic formula has a satisfying assignment. Software designed to solve this problem, known as SAT solvers,
uses techniques such as conflict-driven clause learning (CDCL) and heuristics to efficiently handle large industrial
problem instances.

Satisfiability Modulo Theories (SMT) extends SAT solving by incorporating background theories such as arithmetic,
bit-vectors, and arrays. SMT solvers, like Z3 and CVC5, enable reasoning about more complex constraints beyond Boolean
logic. This allows for more expressive proof scripts and can also lead to performance improvements in automated
reasoning tasks.

Given their critical role in verification and decision procedures, ensuring the correctness of SAT and SMT solvers is
essential. Errors in solver implementations can lead to incorrect proofs and unreliable results. Two main approaches to
achieving correctness guarantees are proof logging and formal verification. Most modern SAT solvers can produce proof
logs in formats such as RAT or DRAT, which can be independently checked by external tools. However, SMT solvers
currently lack standardized proof logging.

Another approach is formal verification, where solvers are implemented within proof assistants like Coq or Isabelle,
ensuring they always produce correct results without requiring external proof checking. While verified SAT solvers
exist, no verified SMT solvers have been developed yet.

## Research question
How can an SMT solver be implemented and formally verified in Coq using transition rules?

## Motivation
SMT solvers are widely used in formal verification, automated reasoning, and decision procedures across various domains,
including software verification, security, and constraint solving. However, their complexity makes them prone to
implementation errors, which can lead to incorrect results and undermine trust in these systems.

While modern SAT solvers support proof logging to enable external proof checking, SMT solvers generally lack
standardized proof logging, making verification of their correctness more challenging. Additionally, existing SMT
solvers are not formally verified, meaning their soundness relies on extensive testing rather than mathematical proof.

A formally verified SMT solver implemented in Coq would provide strong correctness guarantees, ensuring that every
computed result is provably sound. By basing the solver on transition rules, the implementation can be structured in a
way that closely follows formal inference rules, making verification more feasible. This work would bridge the gap
between practical SMT solving and formal verification, offering a trustworthy alternative to existing solver
implementations.
## Approach
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
## Expected outcome
The expected outcome of this research is a formally verified SMT solver, based on transition rules and implemented in
the Coq proof assistant. The solver will be proven to be sound, complete, and terminating.

This work will help bridge the gap between practical SMT solving and formal verification, offering a reliable,
mathematically verified tool for automated reasoning. Furthermore, it will lay the foundation for future work to refine
and implement more advanced verified solvers.


## Related work
See `references.bib` for now.

