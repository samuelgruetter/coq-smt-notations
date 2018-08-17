Require Import Coq.ZArith.ZArith.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Goal forall base a b c d: Z,
  0 <= a < base ->
  0 <= b < base ->
  0 <= c < base ->
  0 <= d < base ->
  base * a + b = base * c + d ->
  b = d.
Proof.
  intros.
  pose proof Z.mod_unique as P.
  specialize P with (b := base) (q := c) (r := d).
  specialize P with (2 := H3).
  rewrite P by omega.
  rewrite <- Z.add_mod_idemp_l by omega.
  rewrite Z.mul_comm.
  rewrite Z.mod_mul by omega.
  rewrite Z.add_0_l.
  rewrite Z.mod_small by omega.
  reflexivity.
Qed.

(* If we turn this goal into smtlib language using the tactics and notations in smt_demo.v,
   we get the following:

    (declare-const a Int)
    (declare-const a0 Int)
    (declare-const a1 Int)
    (declare-const a2 Int)
    (declare-const a3 Int)
    (assert (not (or (not (and (<= 0 a0) (< a0 a)))
                  (or (not (and (<= 0 a1) (< a1 a))) 
                   (or (not (and (<= 0 a2) (< a2 a))) 
                    (or (not (and (<= 0 a3) (< a3 a))) 
                     (or (not (= (+ ( * a a0) a1)
                                 (+ ( * a a2) a3))) 
                         (= a1 a3))))))))
    (check-sat)

but Z3 returns "unknown"
*)
