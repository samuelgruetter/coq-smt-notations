# A Quick Hack

## To ask any SMT solver if your Coq goal is true

Given a goal about integers (Coq's `Z`), you might want to quickly diagnose if it is true or not, before spending too much time trying to prove it.

The file `smt_demo.v` contains some code to do so: First, it uses Ltac to negate the goal, and second, it uses Coq notations the display it in smtlib format, the standard input language for SMT solvers, which can be copy pasted into any SMT solver. If the SMT solver reports `unsat`, it means that no counterexample exists and you should continue proving, if it reports `sat`, you can ask it for a model, which is a counterexample to your theorem.

You can try it out by stepping through `smt_demo.v` in Coq, which contains a sample theorem. However, this sample theorem might look a bit artificial to you, so if you want to see a real-world example where this kind of theorems comes up, you can find the code in action [here](https://github.com/samuelgruetter/riscv-coq/blob/15d8a9747fa459c5eadd0f3c33a122bb946105bd/src/proofs/DecodeEncode.v#L176), and a template without the copy pasted code is [here](https://github.com/samuelgruetter/riscv-coq/blob/03c7f2502a8d83bfb655f994d4d06ec4aea2ddde/src/proofs/DecodeEncode.v#L176).
