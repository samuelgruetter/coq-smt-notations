Require Import Coq.Lists.List.

(* BEGIN library *)

Class SetFunctions(E: Type) := mkSet {
  set: Type;

  contains: set -> E -> Prop;

  empty_set: set;
  singleton_set: E -> set;

  union: set -> set -> set;
  intersect: set -> set -> set;
  diff: set -> set -> set;

  empty_set_spec: forall (x: E), contains empty_set x <-> False;
  singleton_set_spec: forall (x y: E), contains (singleton_set y) x <-> x = y;
  union_spec: forall (x: E) (A B: set), contains (union A B) x <-> contains A x \/ contains B x;
  intersect_spec: forall (x: E) (A B: set), contains (intersect A B) x <-> contains A x /\ contains B x;
  diff_spec: forall (x: E) (A B: set), contains (diff A B) x <-> contains A x /\ ~ contains B x;
}.

Arguments set E {_}.

Notation "x '\in' s" := (contains s x) (at level 39, no associativity).

Section SetDefinitions.
  Context {E: Type}.
  Context {setInst: SetFunctions E}.

  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition remove(s: set E)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_list l := List.fold_right union empty_set (List.map singleton_set l).
End SetDefinitions.

Hint Unfold add subset disjoint : unf_set_defs.

Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  map_domain_set: SetFunctions K;
  map_range_set: SetFunctions V;

  empty_map: map;
  get: map -> K -> option V;
  put: map -> K -> V -> map;
  restrict: map -> set K -> map;
  domain: map -> set K;
  range: map -> set V;
}.

Arguments map _ _ {_}.

(* END library *)


Section DEMO.

  Context (var register: Set).
  Context {allocMap : MapFunctions var register}.
  Notation vars := (@set var (@map_domain_set _ _ allocMap)).
  Existing Instance map_domain_set.

  (* this one holds (SMT solver returns unsat on negation):
  Lemma test: forall (cond : var) (l : vars) (m : map var register) (o : vars),
      (forall a1 a2 : var, a1 \in o -> a2 \in o -> get m a1 = get m a2 -> a1 = a2) ->
      (forall a1 a2 : var, a1 \in l -> a2 \in l -> get m a1 = get m a2 -> a1 = a2) ->
      forall (cws1 ls1 ls2 : vars),
      subset (union ls1 (diff (union (singleton_set cond) ls2) cws1)) o ->
      subset l (union o cws1) ->
      forall (a1 a2 : var),
      a1 \in union (union ls1 (diff (union (singleton_set cond) ls2) cws1)) (diff l cws1) ->
      a2 \in union (union ls1 (diff (union (singleton_set cond) ls2) cws1)) (diff l cws1) ->
      get m a1 = get m a2 -> a1 = a2.
  *)

  (* this one has a counterexample (SMT solver returns sat on negation): *)
  Lemma test: forall (cond : var) (l o : vars) (f0 : var -> option register),
      (forall a1 a2 : var, a1 \in o -> a2 \in o -> f0 a1 = f0 a2 -> a1 = a2) ->
      (forall a1 a2 : var, a1 \in l -> a2 \in l -> f0 a1 = f0 a2 -> a1 = a2) ->
      forall (cws1 ls1 ls2 : vars),
      subset (union ls1 (diff (union (singleton_set cond) ls2) cws1)) o ->
      subset l (union o cws1) ->
      forall a1 a2 : var,
      a1 \in union (union (singleton_set cond) ls2) l ->
      a2 \in union (union (singleton_set cond) ls2) l ->
      f0 a1 = f0 a2 -> a1 = a2.
  Proof.
    intros.

(** BEGIN code to copy paste to translate goal into SMT

Require Import Coq.Logic.Classical_Prop.

Definition marker(P: Prop): Prop := P.
Definition marker2(P: Prop): Prop := P.

Lemma EE: forall AA (P: AA -> Prop), (exists a: AA, ~ P a) <-> ~ forall (a: AA), P a.
Proof.
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro. destruct (classic (exists a : AA, ~ P a)) as [C | C]; [assumption|].
    exfalso. apply H. intro. destruct (classic (P a)) as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Lemma K: forall (P Q: Prop), (~ marker (P -> Q)) <-> marker (~ (P -> Q)).
Proof.
  cbv [marker]. intros. reflexivity.
Qed.

Definition Func(A B: Type) := A -> B.

(* intro as much as we can *)
repeat intro.

(* map to fun *)
repeat match goal with
       | m: map _ _ |- _ =>
         let f := fresh "f" in
         let H := fresh "HE" in
         remember (get m) as f eqn: H;
           clear m H
       end.

(* clear everything except used vars and Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => fail 1
         | _ => clear H
         end
       end.

(* revert all Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => revert H
         end
       end.

(* express set operations in terms of "_ \in _" *)
unfold subset.
repeat (setoid_rewrite union_spec ||
        setoid_rewrite intersect_spec ||
        setoid_rewrite diff_spec).

(* protect functions from being treated as implications *)
repeat match goal with
       | x: ?T1 -> ?T2 |- _ => change (Func T1 T2) in x
       end.

(* mark where hyps begin *)
match goal with
| |- ?G => change (marker G)
end.

(* revert vars *)
repeat match goal with
       | x: ?T |- _ =>
         match T with
         | Type => fail 1
         | SetFunctions _ => fail 1
         | MapFunctions _ _ => fail 1
         | _ => idtac
         end;
           revert x
       end.

(* negate goal *)
match goal with
| |- ?P => assert (~P); [|admit]
end.

(* "not forall" to "exists such that not" *)
repeat match goal with
 | |- context[~ (forall (x: ?T), _)] =>
   (assert (forall (P: T -> Prop), (exists x: T, ~ P x) <-> ~ (forall x: T, P x)) as EEE
    by apply EE);
   setoid_rewrite <- EEE;
   clear EEE
end.

(* push "not" into marker *)
setoid_rewrite K.

(* marker for check_sat *)
match goal with
| |- ?P => change (marker2 P)
end.

(* SMT notations *)
Notation "'forall' '((' a T '))' body" := (forall (a: T), body)
   (at level 10, body at level 0, format "forall  (( a  T )) '//' body", only printing).
Notation "'and' A B" := (Logic.and A B) (at level 10, A at level 0, B at level 0).
Notation "'or' A B" := (Logic.or A B) (at level 10, A at level 0, B at level 0).
Notation "'implies' A B" := (A -> B) (at level 10, A at level 0, B at level 0).
Notation "= A B" := (@eq _ A B) (at level 10, A at level 0, B at level 0, only printing).
Notation "E x" := (contains E x) (at level 10, E at level 0, x at level 0, only printing).
Notation "= x y" := (contains (singleton_set x) y) (at level 10, x at level 0, y at level 0, only printing).
Notation "'not' A" := (not A) (at level 10, A at level 0).
Notation "'(assert' P ')'" := (marker P)
                                (at level 10, P at level 0,
                                 format "(assert  P )").
Notation "'(declare-const' a T ')' body" :=
  (ex (fun (a: T) => body))
    (at level 10, body at level 10,
     format "(declare-const  a  T ')' '//' body").
Notation "'(declare-fun' f '(' A ')' B ')' body" :=
  (ex (fun (f: Func A B) => body))
    (at level 10, body at level 10,
     format "(declare-fun  f  '(' A ')'  B ')' '//' body").
Notation "'(declare-fun' a '(' T ')' 'Bool)' body" :=
  (ex (fun (a: set T) => body))
    (at level 10, body at level 10,
     format "(declare-fun  a  '(' T ')'  'Bool)' '//' body").
Notation "'(declare-sort' 'var)' '(declare-sort' 'reg)' x '(check-sat)' '(get-model)'" :=
  (marker2 x) (at level 200, format "'(declare-sort'  'var)' '//' '(declare-sort'  'reg)' '//' x '//' '(check-sat)' '//' '(get-model)'").
Notation reg := (option register).

(* refresh *)
idtac.

** END code to copy paste to translate goal into SMT *)

  (* Now feed the goal it into Z3, either using the online interface at https://rise4fun.com/z3,
     or using the command "/path/to/local/z3 -smt2 /path/to/file/with/this/goal.smt".

     unsat means your goal is true
     sat   means your goal is false

     If sat, you can interpret the counterexample by commenting out the code between
     BEGIN/END above, and running the code below:

*)

(** BEGIN code to interpret counterexample *)

(* intro as much as we can *)
repeat intro.

(* map to fun *)
repeat match goal with
       | m: map _ _ |- _ =>
         let f := fresh "f" in
         let H := fresh "HE" in
         remember (get m) as f eqn: H;
           clear m H
       end.

(* clear everything except used vars and Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => fail 1
         | _ => clear H
         end
       end.

Notation reg := (option register).

Ltac disj_to_set d :=
  lazymatch d with
    | (_ = ?v1 \/ ?rest) =>
      let s := disj_to_set rest in
      constr:(union (singleton_set v1) s)
    | (_ = ?v1) => constr:(singleton_set v1)
    | _ => fail "did not expect" d
  end.

Ltac universe_of T :=
  let _ := match tt with
           | _ => constr:(@singleton_set T _)
           | _ => fail 1000 "no set instance found for" T
           end in
  match goal with
  | H: forall (x: T), _ |- _ =>
    let dummyT := match type of H with
                  | forall (x: T), x = ?v1 => constr:(v1)
                  | forall (x: T), x = ?v1 \/ _ => constr:(v1)
                  end in
    let P' := type of (H dummyT) in
    disj_to_set P'
  end.

Inductive ____BEGIN_counterexample____: Prop :=
  mk_BEGIN_counterexample: ____BEGIN_counterexample____.
Inductive ____END_counterexample____: Prop :=
  mk_END_counterexample: ____END_counterexample____.
Inductive ____cardinality_constraint: Prop :=
  mk_cardinality_constraint: ____cardinality_constraint.

Tactic Notation "(model" tactic(t) :=
  pose proof mk_BEGIN_counterexample; t.
Tactic Notation ")" :=
  pose proof mk_END_counterexample.
Tactic Notation ";;" "universe" "for" constr(T) ":" tactic(t) := t.
Tactic Notation ";;" ident(v1) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) ident(v3) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) ident(v3) ident(v4) tactic(t) := t.
Tactic Notation ";;" "-----------" tactic(t) := t.
Tactic Notation ";;" "definitions" "for" "universe" "elements:" tactic(t) := t.
Tactic Notation "(declare-fun" ident(x) "()" constr(T) ")" tactic(t) :=
  (assert (x: T) by admit); t.
Tactic Notation "(define-fun" ident(x) "()" constr(T) constr(v) ")" tactic (t) :=
  let E := fresh "E" in (assert (x = v) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" constr(U)
       constr(body) ")" tactic(t) :=
  let E := fresh "E" in (assert (f = fun (x: T) => body) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" "Bool"
       "false" ")" tactic(t) :=
  let E := fresh "E" in (assert (f = empty_set) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" "Bool"
       "true" ")" tactic(t) :=
  let s := universe_of T in
  let E := fresh "E" in (assert (f = s) as E by admit);
  rewrite E in *;
  t.

Tactic Notation ";;" "cardinality" "constraint:" constr(P) tactic(t) :=
  pose proof mk_cardinality_constraint; assert P by admit; t.

(* Gallina notations to parse cardinality constraints: *)
Notation "'forall' '(' '(' a T ')' ')' body" := (forall (a: T), body)
   (at level 200, a at level 0, T at level 0, body at level 0, only parsing).
Notation "'or' A B" := (Logic.or A B)
   (at level 10, A at level 0, B at level 0, only parsing).
Notation "= A B" := (@eq _ A B)
   (at level 10, A at level 0, B at level 0, only parsing).

idtac.

(** END code to interpret counterexample *)

(* now we can copy-paste the output of Z3, add a "." at the end, and replace "!" by "_" : *)

(model
  ;; universe for var:
  ;;   var_val_1 var_val_0
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun var_val_1 () var)
  (declare-fun var_val_0 () var)
  ;; cardinality constraint:
  (forall ((x var)) (or (= x var_val_1) (= x var_val_0)))
  ;; -----------
  ;; universe for reg:
  ;;   reg_val_0
  ;; -----------
  ;; definitions for universe elements:
  (declare-fun reg_val_0 () reg)
  ;; cardinality constraint:
  (forall ((x reg)) (= x reg_val_0))
  ;; -----------
  (define-fun cond () var
    var_val_1)
  (define-fun a2 () var
    var_val_1)
  (define-fun a1 () var
    var_val_0)
  (define-fun l ((x_1 var)) Bool
    false)
  (define-fun f0 ((x_1 var)) reg
    reg_val_0)
  (define-fun ls2 ((x_1 var)) Bool
    true)
  (define-fun cws1 ((x_1 var)) Bool
    true)
  (define-fun o ((x_1 var)) Bool
    false)
  (define-fun ls1 ((x_1 var)) Bool
    false)
).
