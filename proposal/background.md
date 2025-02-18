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
