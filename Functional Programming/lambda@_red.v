(***************************************************)
(* Specification de la théorie de @calcul dans Coq  *)
(*             Lifab-2006-Boumerdes                           *)
(*            (coq version 8)                       *)
(***************************************************)

(* the terms   *)
Require Export Arith.
(* this is the first definition obtened from @-calculu    *)

Inductive terme1 : Set :=
    Var : nat -> terme1
  | Abs : nat -> terme1 -> terme1
  | App : terme1 -> terme1 -> terme1
  | Arobas : nat -> terme1 -> terme1 -> terme1.

(* we add a field to ensure a correct generation of the variable, see afterwards *)

Inductive terme : Set := 
    terme_comp : terme1 -> nat -> terme.

(* les termes sont de la forme  ( n1          ;   n2) pour les variables *)
(*                              ( abs(n, T)   ;   n2) *)
(*                              (App(T1;T2)   ;   n2)*)
(*                              (arobas(T1,T2);   n2)*)

Inductive red  : terme -> terme -> Prop := 

 red1 : forall n1 n2:nat, forall t: terme1,
(red (terme_comp (Arobas n1 (Var n1) t) n2) (terme_comp t n2) )

|red2 : forall n1 n2 n3 :nat,forall t :terme1,
 (~(n1=n2))-> (red (terme_comp
 (Arobas n1 (Var n2) t) n3)
 (terme_comp (Var n2) n3))

|red3 : forall n1 n2 n3 : nat,forall  t1 t2 : terme1, 
(red (terme_comp (Arobas n1(Abs n2 t1) t2) n3)
     (terme_comp (Abs n3(Arobas n1(Arobas n2 t1 (Var n3)) t2)) (S n3)))

|red4 :forall n1 n2 : nat, forall t1 t2 t3 :terme1, 
(red (terme_comp (Arobas n1 (App t1 t2)t3)n2)
     (terme_comp (App (Arobas n1 t1 t3)(Arobas n1 t2 t3))n2))

|red5: forall n1 n2:nat, forall t1 t2:terme1,
(red(terme_comp (App(Abs n1 t1)t2)n2) 
    (terme_comp(Arobas n1 t1 t2)n2))

|red6:forall n1 n2:nat, forall t1 t2:terme1, 
(red(terme_comp t1 n1)(terme_comp t2 n2))-> forall n : nat,
(red (terme_comp (Abs n t1) n1)(terme_comp (Abs n t2) n2))

|red7: forall n1 n2 :nat, forall t1 t2: terme1,
(red (terme_comp t1 n1)(terme_comp t2 n2)) -> forall t3 :terme1, 
(red (terme_comp (App t3 t1) n1)(terme_comp (App t3 t2)n2))

|red8: forall n1 n2: nat, forall t1 t2 : terme1, 
(red (terme_comp t1 n1) (terme_comp t2 n2)) -> forall t3 : terme1, 
(red (terme_comp (App t1 t3) n1) (terme_comp (App t2 t3) n2 ))

|red9: forall n1 n2: nat, forall t1  t2 : terme1, 
(red (terme_comp t1 n1) (terme_comp t2 n2)) -> 
forall n : nat, forall t3:terme1,(red(terme_comp(Arobas n t1 t3) n1) 
                                  (terme_comp (Arobas n t2 t3)n2)).
 
 
(************************************************************)
Definition normal  (T : terme) := ( forall U : terme, ~(red T U)).
(********************************************************************)
Definition red_fun (T : terme) := {U : terme| (red T U)} + {normal T}.


 (******************************************************************)

Lemma nat_dec : forall n n0 : nat, {(n = n0)} + {~(n = n0)}.

decide equality.
Qed.

(**************************************************)

Lemma Var_normal : forall n1 n2 : nat, (normal (terme_comp (Var n1) n2)).
unfold normal.
unfold not.
intros.
inversion H.
Qed.

(**********************************************************)

Theorem cbred : forall t: terme, (red_fun t).
intro.
elim t.
intros.
elim t0.
unfold red_fun.
right. apply Var_normal.

unfold red_fun.
intros.
inversion H; clear H.
elim H0; clear H0; intro.
case x; intros.
left.
split with (terme_comp (Abs n0 t2) n1).
apply red6.
exact p.

right; generalize H0; clear H0; unfold normal; unfold not; intros.
inversion H; clear H.
generalize (H0 (terme_comp t3 n2)); intros.
absurd (red (terme_comp t1 n) (terme_comp t3 n2));
  [ red; assumption | assumption ].

intro.
case t1.
unfold red_fun; intros.
inversion H0; clear H0.
elim H1.
clear H1.
intro.
case x.
intro.
intros.
left.
split with (terme_comp (App (Var n0) t3) n1).
apply red7.
exact p.

right; generalize H1; clear H1; unfold normal; unfold not; intros.
inversion H0; clear H0.
generalize (H1 (terme_comp t4 n2)); intros.
absurd (red (terme_comp t2 n) (terme_comp t4 n2));
  [ red; assumption | assumption ].

inversion H6.

intro; intro.
intros.
unfold red_fun.
left.

split with (terme_comp (Arobas n0 t2 t3) n).
apply red5.

unfold red_fun; intros.
inversion H; clear H.
elim H1; clear H1; intro.
case x.
intros.
left; split with (terme_comp (App t5 t4) n0).
apply red8.
exact p.

inversion H0; clear H0.
elim H; clear H; intro.
case x.
intros.
left; split with (terme_comp (App (App t2 t3) t5) n0).
apply red7.
exact p.

right; generalize H; generalize H1; clear H; clear H1; unfold normal;
  unfold not; intros.
inversion H0; clear H0.
generalize (H (terme_comp t6 n2)); intros;
  absurd (red (terme_comp t4 n) (terme_comp t6 n2));
  [ red; assumption | assumption ].

generalize (H1 (terme_comp t6 n2)); intros;
  absurd (red (terme_comp (App t2 t3) n) (terme_comp t6 n2));
  [ red; assumption | assumption ].

unfold red_fun; intros.
inversion H; clear H.
elim H1; clear H1; intro.
case x; intros.
left.
split with (terme_comp (App t5 t4) n1).
apply red8; assumption.

inversion H0; clear H0.
elim H; clear H; intro.
case x; intros.
left.
split with (terme_comp (App (Arobas n0 t2 t3) t5) n1).
apply red7.
exact p.

right; generalize H; generalize H1; clear H; clear H1; unfold normal;
  unfold not; intros.
inversion H0; clear H0.
generalize (H (terme_comp t6 n2)); intros;
  absurd (red (terme_comp t4 n) (terme_comp t6 n2));
  [ red; assumption | assumption ].

generalize (H1 (terme_comp t6 n2)); intros;
  absurd (red (terme_comp (Arobas n0 t2 t3) n) (terme_comp t6 n2));
  [ red; assumption | assumption ].

intro.
intro.
case t1.
intros; unfold red_fun; left.
cut ({n0=n1}+{~n0=n1}).
intros.
inversion H1; clear H1.
rewrite H2.
split with (terme_comp t2 n).
apply red1; assumption.

unfold not in H2.
split with (terme_comp (Var n1) n).
apply red2.
red; assumption.

apply nat_dec.

intros.
unfold red_fun; left.
split
 with (terme_comp (Abs n (Arobas n0 (Arobas n1 t2 (Var n)) t3)) (S n)).
apply red3.

unfold red_fun; intros.
inversion H; clear H; clear H0.
elim H1; clear H1; intro.
case x.
intros.
left.
split with (terme_comp (Arobas n0 t5 t4) n1).
apply red9.
exact p.

left.
split with (terme_comp (App (Arobas n0 t2 t4) (Arobas n0 t3 t4)) n).
apply red4.

unfold red_fun.
intros.
inversion H; clear H.
left; elim H1; clear H1.
intro; case x; intros.
split with (terme_comp (Arobas n0 t5 t4) n2).
apply red9.
exact p.

right; generalize H1; clear H1; unfold normal; unfold not; intros.
inversion H.
generalize (H1 (terme_comp t6 n3)).
intros.
absurd (red (terme_comp (Arobas n1 t2 t3) n) (terme_comp t6 n3));
  [ red; assumption | assumption ].

Qed.

	
	Extraction "reduc" cbred.



