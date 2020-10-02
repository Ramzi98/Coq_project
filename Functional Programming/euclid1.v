Require Import Peano_dec.
Require Import Arith.
Require Import Omega.
Require Extraction.

Open Scope   nat_scope.

Implicit Types a b n q r : nat.

Inductive diveucl a b : Set :=
 divex : forall q r, (b > r)-> ~(b = O) -> (a= q * b + r) -> diveucl a b.

Lemma eucl_dev : forall n, (n>0) -> forall m:nat, diveucl m n.

Proof.

induction  m.
constructor 1 with 0 0.
 trivial.
SearchAbout "~".

apply Nat.neq_0_lt_0.
trivial.



(simpl; trivial).
destruct IHm.
(*elim (eq_nat_dec 0 (S  0)).  intros. inversion a.
intro.*)
elim (eq_nat_dec n (S r)).    intro.
exists  (S q) 0; trivial.
rewrite e. simpl.  omega. intro.
exists q (S r). omega. trivial.
rewrite e. omega.
Qed.
Extraction "euclid"  eucl_dev.