# A Quick Hack

## To ask any SMT solver if your Coq goal is true

Given a goal about integers (Coq's `Z`), you might want to quickly diagnose if it is true or not, before spending too much time trying to prove it.

The file `smt_demo.v` contains some code to do so: First, it uses Ltac to negate the goal, and second, it uses Coq notations the display it in smtlib format, the standard input language for SMT solvers, which can be copy pasted into any SMT solver. If the SMT solver reports `unsat`, it means that no counterexample exists and you should continue proving, if it reports `sat`, you can ask it for a model, which is a counterexample to your theorem.
