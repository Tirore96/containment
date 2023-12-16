From mathcomp Require Import all_ssreflect zify.
From Containment Require Import tactics utils regex.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Type PredL.
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
End PredL.

Module Type Pred.
Parameter A : finType.
Implicit Type (r : @regex A).
Implicit Type (l : @pder A).
Implicit Type (s : @trace A).
(*Notation regex := (@regex A).
Notation pder := (@pder A).*)

Parameter (P: forall s, @regex A -> @regex A -> Prop).
Parameter (Pb : @regex A -> @regex A -> bool).
(*Axiom derive_pd_l : forall l e, forall s, P s (e \ \big[Plus/Empt]_(i <- l) i) 
                                   (\big[Plus/Empt]_(i <- pd_l e l) i).*)
Axiom Pb_P_iff : forall r r'', Pb r r'' <->
                      P [::] r r''.
Axiom P_derive : forall a r0 r1,forall s, P s (a \ r0) (a \ r1) <-> P (a :: s) r0 r1.

(*Axiom P_undup : forall l0 l1, (forall s, P s l0 l1 <-> P s (undup l0) (undup l1)). *)
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

Module EquivF (M : FModule) <: PredL.
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


Module ContainsF (M : FModule) <: PredL.
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


Module Type Axiom_Type (M : FModule).
Import M.
Parameter dsl: (@regex A ->  @regex A -> Type) -> @regex A -> @regex A -> Type. 
Parameter Add : (@regex A ->  @regex A -> Type) -> (@regex A) -> (@regex A) ->(@regex A -> @regex A -> Type). 

Axiom dsl_mon : forall l l' E F, dsl l E F -> (forall x y, l x y -> l' y x) ->  dsl l' E F.

Section AxiomSection.
Variable (R :  (@regex A -> @regex A -> Type )).
Axiom shuffle : forall A B C, dsl R ((A _+_ B) _+_ C) (A _+_ (B _+_ C)).
Axiom shuffleinv : forall A B C,  dsl R (A _+_ (B _+_ C)) ((A _+_ B) _+_ C).
Axiom retag : forall A B, dsl R (A _+_ B) (B _+_ A).
Axiom untagL : forall A, dsl R (Empt _+_ A) A.
Axiom untagLinv : forall A, dsl R A  (Empt _+_ A).
Axiom untag : forall A, dsl R (A _+_ A)  A.
Axiom tagL : forall A B, dsl R A  (A _+_ B ).

Axiom assoc : forall A B C, dsl R ((A _;_ B) _;_ C)  (A _;_ (B _;_ C)). 
Axiom associnv : forall A B C, dsl R (A _;_ (B _;_ C))   ((A _;_ B) _;_ C).

Axiom swap : forall A,  dsl R (A _;_ Eps)  (Eps _;_ A). 
Axiom swapinv : forall A, dsl R(Eps _;_ A)  (A _;_ Eps). 

Axiom proj : forall A, dsl R (Eps _;_ A)  A. 
Axiom projinv : forall A, dsl R A (Eps _;_ A). 

Axiom abortR : forall A, dsl R (A _;_ Empt)  Empt.
Axiom abortRinv : forall A, dsl R Empt   (A _;_ Empt).

Axiom abortL : forall A, dsl R (Empt _;_ A)   Empt. 
Axiom abortLinv : forall A, dsl R Empt    (Empt _;_ A).

Axiom distL : forall A B C, dsl R (A _;_ (B _+_ C))  ((A _;_ B) _+_ (A _;_ C)).
Axiom distLinv : forall A B C, dsl R  ((A _;_ B) _+_ (A _;_ C)) (A _;_ (B _+_ C)).

Axiom distR : forall A B C, dsl R ((A _+_ B) _;_ C)  ((A _;_ C) _+_ (B _;_ C)).
Axiom distRinv : forall A B C, dsl R ((A _;_ C) _+_ (B _;_ C))   ((A _+_ B) _;_ C).

Axiom wrap : forall A, dsl R (Eps _+_ (A _;_ Star A))  (Star A).
Axiom wrapinv : forall A, dsl R (Star A)  (Eps _+_ (A _;_ Star A)).

Axiom drop : forall A, dsl R  (Star (Eps _+_ A))  (Star A).
Axiom dropinv : forall A, dsl R (Star A)  (Star (Eps _+_ A)).
Axiom cid : forall A, dsl R A A. 

(*Axiom ci_sym A B (H: A =R=B) : B =R=A*)
Axiom ctrans : forall A B C, dsl R  A B ->  dsl R B C -> dsl R A C.
Axiom cplus : forall A A' B B',  dsl R A A'  -> dsl R B B' -> dsl R  (A _+_ B) (A' _+_ B').
Axiom cseq : forall A A' B B', dsl R A A' -> dsl R B B' ->  dsl R (A _;_ B) (A' _;_ B').
Axiom cstar : forall A B, dsl R  A B -> dsl R (Star A)  (Star B).
(*Axiom rule_cfix r r' (p  : dsl R dsl) : dsl R r  r' ~> p[d (cfix p) .: dsl R var_dsl] ->  r  r' ~> (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dsl R ((Event a) _;_ A)  ((Event a) _;_ B)*)
(*| dsl_var a A B n : PTree.get n R = Some (A,B) -> dsl R ((Event a) _;_ A) ((Event a) _;_ B) *)
Axiom dsl_var : forall a A B,   R A B -> dsl R (Event a _;_ A) (Event a _;_  B). 

(*without summation as that was due to productivity checker, not needed for inductive definition*)
Axiom dsl_fix : forall A B,  dsl (Add R A B) A B -> dsl R A B.
End AxiomSection.
End Axiom_Type.
