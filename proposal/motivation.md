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