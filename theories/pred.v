From mathcomp Require Import all_ssreflect zify.
From Containment Require Import  regex.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Type Pred.
Parameter A : finType.
Implicit Type (r : @regex A).
Implicit Type (l : @pder A).
Implicit Type (s : @trace A).
(*Notation regex := (@regex A).
Notation pder := (@pder A).*)

Parameter (P: forall s, @regex A -> @regex A -> Prop).
Parameter (Pb : @pder A -> @pder A -> bool).
(*Axiom derive_pd_l : forall l e, forall s, P s (e \ \big[Plus/Empt]_(i <- l) i) 
                                   (\big[Plus/Empt]_(i <- pd_l e l) i).*)
Axiom Pb_P_iff : forall l l', Pb l l' <->
                      P [::] (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i).
Axiom P_derive : forall a l0 l1,forall s, P s (\big[Plus/Empt]_(i <- (pd_l a l0)) i) (\big[Plus/Empt]_(i <- (pd_l a l1)) i) <-> P (a :: s) (\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i).
Axiom P_undup : forall l0 l1, (forall s, P s (\big[Plus/Empt]_(i <- l0) i) (\big[Plus/Empt]_(i <- l1) i) <-> P s (\big[Plus/Empt]_(i <- undup l0) i) (\big[Plus/Empt]_(i <- undup l1) i)).
Axiom P_empt :  forall r0 r1, forall s, P s (r0 _+_ Empt) (r1 _+_ Empt) <-> P s r0 r1. 

End Pred.



