From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
Require Import Relation_Definitions Setoid.
Require Import Coq.btauto.Btauto.
Require Import Paco.paco.
From Containment Require Import  tactics utils regex enum pred extensional_partial modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Let inE := tactics.inE.

Module Equivalence_on (M : FModule).
Module FM := EquivF M.
Module MyExt := ExtensionalPartial FM.
Import FM MyExt.
Implicit Types (r : @regex A).

Section CoInductive_Equivalence.
  Variable co_eq : @regex A -> @regex A -> Prop.
Reserved Notation "c0 =R= c1" (at level 63).
(*Maybe c_star_ctx and c_star_plus are not necessary*)

Inductive c_eqc : regex -> regex -> Prop :=
| c_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
| c_plus_comm c0 c1: c0 _+_ c1 =R= c1 _+_ c0
| c_plus_neut c: c _+_ Empt =R= c
| c_plus_idemp c : c _+_ c =R= c 
| c_seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
| c_seq_neut_l c : (Eps _;_ c) =R= c 
| c_seq_neut_r c : c _;_ Eps =R= c 
| c_seq_failure_l c : Empt _;_ c =R= Empt  
| c_seq_failure_r c :  c _;_ Empt =R= Empt 
| c_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
| c_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)

| c_unfold c :  Eps _+_ (c _;_ Star c) =R= Star c (*New star rule 1*)
| c_star_plus c :  Star (Eps _+_ c) =R= Star c (*New star rule 2*)
| c_refl c : c =R= c
| c_sym c0 c1 (H: c0 =R=c1) : c1 =R=c0
| c_trans c0 c1 c2 (H1 : c0 =R=c1) (H2 : c1 =R=c2) : c0 =R=c2
| c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _+_ c1 =R=c0' _+_ c1'
| c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _;_ c1 =R=c0' _;_ c1'
| c_star_ctx c0 c1 (H : c0 =R=c1) : Star c0 =R= Star c1  (*new context rule*) 
| c_fix a c0 c1 : co_eq c0 c1 ->  Event a _;_ c0 =R= Event a _;_ c1
 where "c1 =R= c2" := (c_eqc c1 c2).
End CoInductive_Equivalence.
Hint Constructors c_eqc.
Lemma c_eqc_gen_mon: monotone2 c_eqc. 
Proof.
unfold monotone2.
intros. induction IN; eauto. 
Qed.
Hint Resolve c_eqc_gen_mon : paco.
Notation "c0 = ⟪ R ⟫ = c1" := (c_eqc R c0 c1)(at level 63).
Definition CO_EQ c0 c1 := paco2 c_eqc bot2 c0 c1.



Definition IND_EQ c0 c1 := ?






Reserved Notation " l |- c0 =R= c1" (at level 63).
Inductive c_eq ( l : seq (@regex A  * regex)) : regex -> regex -> Prop :=
| c2_plus_assoc c0 c1 c2 : l |- (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
| c2_plus_comm c0 c1: l |- c0 _+_ c1 =R= c1 _+_ c0
| c2_plus_neut c : l |-  c _+_ Empt =R= c
| c2_plus_idemp c  : l |- c _+_ c =R= c 
| c2_seq_assoc c0 c1 c2  : l |- (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
| c2_seq_neut_l c : l |- (Eps _;_ c) =R= c 
| c2_seq_neut_r c : l |-  c _;_ Eps =R= c 
| c2_seq_failure_l c : l |- Empt _;_ c =R= Empt  
| c2_seq_failure_r c :  l |-c _;_ Empt =R= Empt 
| c2_distr_l c0 c1 c2 : l |- c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
| c2_distr_r c0 c1 c2 : l |- (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)

| c2_unfold c : l |-  Eps _+_ (c _;_ Star c) =R= Star c (*New star rule 1*)
| c2_star_plus c : l |-  Star (Eps _+_ c) =R= Star c (*New star rule 2*)
| c2_refl c : l |- c =R= c
| c2_sym c0 c1 (H: l |- c0 =R=c1) : l |- c1 =R=c0
| c2_trans c0 c1 c2 (H1 : l |- c0 =R=c1) (H2 : l |- c1 =R=c2) : l |- c0 =R=c2
| c2_plus_ctx c0 c0' c1 c1' (H1 : l |- c0 =R=c0') 
                             (H2 : l |- c1 =R=c1') : l |- c0 _+_ c1 =R=c0' _+_ c1'
| c2_seq_ctx c0 c0' c1 c1'  (H1 : l |- c0 =R=c0') 
                             (H2 : l |- c1 =R=c1') : l |-  c0 _;_ c1 =R=c0' _;_ c1'
| c2_star_ctx c0 c1         (H :  l |- c0 =R=c1) : l |- Star c0 =R= Star c1  (*new context rule*) 
| c2_var a c0 c1 : (c0, c1) \in l -> l |-  Event a _;_ c0 =R= Event a _;_ c1
| c2_fix c0 c1 :  (c0,c1)::l |- c0 =R= c1 ->  l |-  c0 =R= c1
(*| c_add r r' : (r,r')::l |- r =R= r'  -> l |- r =R= r'*)
 where "l |- c1 =R= c2" := (c_eq l c1 c2).
Hint Constructors c_eq.
Notation "c0 = ⟨ R ⟩ = c1" := (c_eq R c0 c1)(at level 63).


Add Parametric Relation R : regex (@c_eq R)
  reflexivity proved by (c2_refl R)
  symmetry proved by (@c2_sym R)
  transitivity proved by (@c2_trans R)
  as regex_setoid2.

Add Parametric Morphism R : Plus with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as c_eqc_plus_morphism2.
Proof.
intros. eauto. 
Qed.

Add Parametric Morphism R : Seq with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as co_eq_seq_morphism2.
Proof.
intros. eauto.
Qed.

Add Parametric Morphism R : Star with
signature (c_eq R) ==> (c_eq R) as c_eqc_star_morphism2.
Proof.
intros. eauto.
Qed.





