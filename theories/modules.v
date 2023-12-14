From mathcomp Require Import all_ssreflect zify.
From Containment Require Import tactics utils regex.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Type Pred.
Parameter A : finType.
Implicit Type (r : @regex A).
Implicit Type (l : @pder A).
Implicit Type (s : @trace A).
(*Notation regex := (@regex A).
Notation pder := (@pder A).*)

Parameter (P: forall s, @pder A -> @pder A -> Prop).
Parameter (Pb : @pder A -> @pder A -> bool).
(*Axiom derive_pd_l : forall l e, forall s, P s (e \ \big[Plus/Empt]_(i <- l) i) 
                                   (\big[Plus/Empt]_(i <- pd_l e l) i).*)
Axiom Pb_P_iff : forall l l', Pb l l' <->
                      P [::] l l'.
Axiom P_derive : forall a l0 l1,forall s, P s (pd_l a l0) (pd_l a l1) <-> P (a :: s) l0 l1.

Axiom P_undup : forall l0 l1, (forall s, P s l0 l1 <-> P s (undup l0) (undup l1)).  
(*(\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i) <-> P s (\big[Plus/Empt]_(i <- undup l0) i) (\big[Plus/Empt]_(i <- undup l1) i)).*)
(*Axiom P_empt :  forall r0 r1, forall s, P s (r0 _+_ Empt) (r1 _+_ Empt) <-> P s r0 r1. *)

(*Axiom Pb_P_iff : forall l l', Pb l l' <->
                      P [::] (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i).
Axiom P_derive : forall a l0 l1,forall s, P s (\big[Plus/Empt]_(i <- (pd_l a l0)) i) (\big[Plus/Empt]_(i <- (pd_l a l1)) i) <-> P (a :: s) (\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i).
Axiom P_undup : forall l0 l1, (forall s, P s (\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i) <-> P s (\big[Plus/Empt]_(i <- undup l0) i) (\big[Plus/Empt]_(i <- undup l1) i)).
Axiom P_empt :  forall r0 r1, forall s, P s (r0 _+_ Empt) (r1 _+_ Empt) <-> P s r0 r1. *)
End Pred.

Module Type FModule.
Parameter (A : finType).
End FModule.

Module EquivF (M : FModule) <: Pred.
Definition A := M.A. 
Definition P s (l0 l1 : @pder A) := Match s (\big[Plus/Empt]_(a <- l0) a) <-> Match s (\big[Plus/Empt]_(a <- l1) a).
Definition Pb := (fun ( l0 l1 : @pder A) => has nu l0 == has nu l1).

Lemma Pb_P_iff : forall l l', Pb l l' <->
                           P [::] l l'.
Proof.
intros. rewrite /P /Pb. 
rewrite -!Match_has_nu_iff. split. move/eqP=>->//. move/eq_iff=>->//.
Qed.

Lemma P_derive : forall a l0 l1, forall s, P s  (pd_l a l0) (pd_l a l1) <-> P (a :: s) l0 l1.  
Proof.
intros. rewrite /P.
rewrite -!pd_plus. rewrite !Match_big_undup.
rewrite !deriveP2. done.
Qed.

Lemma P_undup : forall l0 l1, (forall s, P s l0 l1  <-> P s (undup l0) (undup l1)).
Proof.
intros. rewrite /P. rewrite !Match_big_undup //.
Qed.

(*Lemma P_empt_aux : forall s r, P s (r _+_ Empt) r.
Proof.
intros. rewrite /P. split;ssa. inv H. inv H2. con. done.
Qed.
Lemma P_empt :  forall r0 r1, forall s, P s (r0 _+_ Empt) (r1 _+_ Empt) <-> P s (r0) (r1).
Proof.
intros. rewrite /P. 
move: (P_empt_aux s). rewrite /P.  move=> HH. rewrite !HH //.
Qed.*)
End EquivF.


Module ContainsF (M : FModule) <: Pred.
Definition A := M.A. 
Definition P s (l0 l1 : @pder A) := Match s (\big[Plus/Empt]_(a <- l0) a) -> Match s (\big[Plus/Empt]_(a <- l1) a).
Definition Pb := (fun ( l0 l1 : @pder A) => has nu l0 ==> has nu l1).

Lemma Pb_P_iff : forall l l', Pb l l' <->
                           P [::] l l'.
Proof.
intros. rewrite /P /Pb. 
rewrite -!Match_has_nu_iff. split. move/implyP=>//.  
move/implyP=>//.
Qed.

Lemma P_derive : forall a l0 l1, forall s, P s  (pd_l a l0) (pd_l a l1) <-> P (a :: s) l0 l1.  
Proof.
intros. rewrite /P.
rewrite -!pd_plus. rewrite !Match_big_undup.
rewrite !deriveP2. done.
Qed.


Lemma P_undup : forall l0 l1, (forall s, P s l0 l1  <-> P s (undup l0) (undup l1)).
Proof.
intros. rewrite /P. rewrite !Match_big_undup //.
Qed.


(*Lemma P_empt_aux : forall s r, P s (r _+_ Empt) r.
Proof.
intros. rewrite /P. split;ssa. inv H. inv H2. con. done.
Qed.
Lemma P_empt :  forall r0 r1, forall s, P s (r0 _+_ Empt) (r1 _+_ Empt) <-> P s (r0) (r1).
Proof.
intros. rewrite /P. 
move: (P_empt_aux s). rewrite /P.  move=> HH. rewrite !HH //.
Qed.*)
End ContainsF.


(*Module MyPredF2 (M : FModule) <: Pred.
Definition A := M.A. 
Definition P s (r0 r1 : @regex A) := Match s r0 -> Match s r1.
Definition Pb := (fun ( l0 l1 : @pder A) => has nu l0 ==> has nu l1).

Lemma Pb_P_iff : forall l l', Pb l l' <->
                           P [::] (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. rewrite /P /Pb. 
rewrite -!Match_has_nu_iff. split. move/implyP=>//.  
move/implyP=>//.
Qed.

Lemma P_derive : forall a l0 l1,forall s, P s (\big[Plus/Empt]_(i <- (pd_l a l0)) i) (\big[Plus/Empt]_(i <- (pd_l a l1)) i) <-> P (a :: s) (\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i).
Proof.
intros. rewrite /P.
rewrite -!pd_plus. rewrite !Match_big_undup.
rewrite !deriveP2. done.
Qed.

Lemma P_undup : forall l0 l1, (forall s, P s (\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i) <-> P s (\big[Plus/Empt]_(i <- undup l0) i) (\big[Plus/Empt]_(i <- undup l1) i)).
Proof.
intros. rewrite /P. rewrite !Match_big_undup //.
Qed.

Lemma P_empt_aux : forall s r, P s (r _+_ Empt) r.
Proof.
intros. rewrite /P.  ssa. inv H. inv H2. 
Qed.

Lemma P_empt :  forall r0 r1, forall s, P s (r0 _+_ Empt) (r1 _+_ Empt) <-> P s (r0) (r1).
Proof.
intros. rewrite /P. split. intros.
have: Match s (r0 _+_ Empt). con. done. move/H. move=>HH. inv HH. inv H3.
intros. inv H0. con. eauto. inv H3.
Qed.
End MyPredF2.*)
