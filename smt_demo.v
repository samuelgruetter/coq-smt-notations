Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Lemma test: forall
  (opcode rs1 rs2 funct3 simm12
  inst q q0 r1 r2
  r r0 q1 q2 q3 r3 q4 r4 q5 r5 q6 r6 q7 r7 q8 r8 q9 r9 q10 r10 q11 r11 q12
  r12 q13 r13 q14 r14 q15 r15 q16 r16: Z),
    0 <= opcode < 128 /\ 0 <= rs1 < 32 /\ 0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\ - (2048) <= simm12 < 2048
  -> opcode + r1 * 128 + funct3 * 4096 + rs1 * 32768 + rs2 * 1048576 + r2 * 33554432 = inst
  -> 0 <= r16 < 2
  -> q9 = 2 * q16 + r16
  -> 0 <= r15 < 32
  -> q6 = 32 * q15 + r15
  -> 0 <= r14 < 32
  -> q5 = 32 * q14 + r14
  -> 0 <= r13 < 8
  -> q4 = 8 * q13 + r13
  -> 0 <= r12 < 128
  -> q3 = 128 * q12 + r12
  -> 0 <= r11 < 32
  -> q8 = 32 * q11 + r11
  -> 0 <= r10 < 128
  -> q7 = 128 * q10 + r10
  -> 0 <= r9 < 2048
  -> r10 * 32 + r11 = 2048 * q9 + r9
  -> 0 <= r8 < 128
  -> inst = 128 * q8 + r8
  -> 0 <= r7 < 33554432
  -> inst = 33554432 * q7 + r7
  -> 0 <= r6 < 1048576
  -> inst = 1048576 * q6 + r6
  -> 0 <= r5 < 32768
  -> inst = 32768 * q5 + r5
  -> 0 <= r4 < 4096
  -> inst = 4096 * q4 + r4
  -> 0 <= r3 < 1
  -> inst = 1 * q3 + r3
  -> 0 <= r2 < 128
  -> q0 = 128 * q2 + r2
  -> 0 <= r1 < 32
  -> q = 32 * q1 + r1
  -> 0 <= r0 < 32
  -> simm12 = 32 * q0 + r0
  -> 0 <= r < 1
  -> simm12 = 1 * q + r
  -> opcode = r12 /\ funct3 = r13 /\ rs1 = r14
     /\ rs2 = r15 /\ simm12 = r10 * 32 + r11 - r16 * 4096.
Proof.
  intros.
  Fail omega.
  Fail Timeout 10 lia.
  Fail Timeout 10 nia.

(** BEGIN goal negation code *)

Require Import Coq.Logic.Classical_Prop.

Definition marker(P: Prop): Prop := P.
Definition marker2(P: Prop): Prop := P.

Lemma E: forall A (P: A -> Prop), (exists a: A, ~ P a) <-> ~ forall (a: A), P a.
Proof.                                                                                
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro. destruct (classic (exists a : A, ~ P a)) as [C | C]; [assumption|].
    exfalso. apply H. intro. destruct (classic (P a)) as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Lemma K: forall (P Q: Prop), (~ marker (P -> Q)) <-> marker (~ (P -> Q)).
Proof.
  cbv [marker]. intros. reflexivity. 
Qed.

Ltac countZ t :=
  lazymatch t with
  | forall (x: Z), @?t' x =>
    let a := eval cbv beta in (t' 0) in
        let r := countZ a in constr:(S r)
  | _ => constr:(O)
  end.

Ltac repeatN N f :=
  match N with
  | S ?n => f; repeatN n f
  | O => idtac
  end.

Ltac negate_goal :=
  repeat match goal with
         | H: ?T |- _ => match T with
                         | Z => fail 1
                         | _ => revert H
                         end
         end;
  match goal with
  | |- ?P => change (marker P)
  end;
  repeat match goal with
         | H: _ |- _ => revert H
         end;
  match goal with
  | |- ?P => assert (~P); [|admit]
  end;
  match goal with
  | |- ~ ?P => let r := countZ P in repeatN r ltac:(setoid_rewrite <- E)
  end;
  setoid_rewrite K;
  match goal with
  | |- ?P => change (marker2 P)
  end.

Set Printing Depth 10000.

negate_goal.

(** END goal negation code *)

(** BEGIN notations *)

Notation "'and' A B" := (Logic.and A B) (at level 10, A at level 0, B at level 0).
Notation "'or' A B" := (Logic.or A B) (at level 10, A at level 0, B at level 0).
Notation "+ A B" := (Z.add A B) (at level 10, A at level 0, B at level 0).
Notation "< A B" := (Z.lt A B) (at level 10, A at level 0, B at level 0).
Notation "<= A B" := (Z.le A B) (at level 10, A at level 0, B at level 0).
Notation "- A B" := (Z.sub A B) (at level 10, A at level 0, B at level 0).
Notation "* A B" := (Z.mul A B) (at level 10, A at level 0, B at level 0, format " *  A  B").
Notation "= A B" := (@eq Z A B) (at level 10, A at level 0, B at level 0).
Notation "'not' A" := (not A) (at level 10, A at level 0).
Notation "'(declare-const' a 'Int)' body" :=
  (ex (fun (a: Z) => body))
    (at level 10, body at level 10,
     format "(declare-const  a  Int) '//' body").
Notation "'(assert' P ')'" := (marker P)
                                (at level 10, P at level 0,
                                 format "(assert  P )").
Notation "- 0 a" := (Z.opp a) (at level 10, a at level 10).
Notation "'or' '(not' A ')' B" := (A -> B) (at level 10, A at level 0, B at level 0,
                                            format "or  (not  A )  B").
Notation "x '(check-sat)'" := (marker2 x) (at level 200, format "x '//' '(check-sat)'").

idtac.

(** END notations *)


  (* Now feed the goal it into Z3.
     unsat means your goal is true
     sat   means your goal is false *)

