From mathcomp Require Import all_ssreflect zify.
Require Import Paco.paco.
From Containment Require Import tactics utils regex enum modules extensional_partial.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

(*Module Type Pred2.

Axiom P_r_derive : forall r0 r1 e, (forall s, P s r0 r1) -> (forall s,P s (e \ r0) (e \ r1)).
Axiom P_r_trans : forall r0 r1 r2, (forall s, P s r0 r1) -> (forall s, P s r1 r2) -> (forall s, P s r0 r2).
Axiom P_r_sym : forall r0 r1, (forall s, P s r0 r1) -> (forall s,P s r1 r0). *)



Module ExtensionalDerivative (M : Pred).
Module EP := ExtensionalPartial M.
Import M EP.


End Extensional.
