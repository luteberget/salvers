# Salvers

Various SAT-based Rust libraries for logic and optimization. Everything is very much **experimental** and for educational purposes.

 * **`sattrait`**: Trait for calling SAT solvers, and interface for theories.
 * **`dpllt`**: SAT solver, mostly ported from Minisat v.2.2, with dynamic refinement callbacks (a.k.a. theory support).
 * **`idl`**: graph-based solver for integer difference logic.
 * **`rc2`**: MaxSAT algorithm, very basic implementation of `https://pysathq.github.io/docs/html/api/examples/rc2.html`.
 * **`totalizer`**: Incremental totalizer for pseudo-boolean constraints.
 * **`scheduleopt`**: experimental backend for scheduling optimization problems using dynamic longest paths and and RC2-like SMT-based algorithm for optimization.

