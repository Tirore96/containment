From mathcomp Require Import all_ssreflect zify.
From Containment Require Import tactics utils regex modules extensional_partial.
Set Implicit Arguments.
Set Maximal Implicit Insertion.


Module TM <: FModule.
Print FModule.
Definition A := (ordinal 100 : finType).
End TM.

Module MP := EquivF TM.
Module EP := ExtensionalPartial MP.
Import MP EP. 

Lemma equiv_r_dec_aux : forall (r0 r1 : @regex A), bisim_wrap (r0::nil) (r1::nil) <-> equiv_r r0 r1. 
Proof. intros. rewrite P_decidable /P. rewrite equiv_seq1. done. Qed.

Lemma equiv_r_dec : forall (r0 r1 : @regex A), { equiv_r r0 r1} + { ~ equiv_r r0 r1}.
Proof. intros. destruct (bisim_wrap (r0::nil) (r1::nil)) eqn:Heqn. con.
apply/equiv_r_dec_aux. done. constructor 2. 
intro. apply equiv_r_dec_aux in H. rewrite Heqn in H. done.
Qed.

Print Assumptions equiv_r_dec.
Print Assumptions bisim_sound.

Print Assumptions Equations.Prop.Subterm.
