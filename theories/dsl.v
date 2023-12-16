From HB Require Import structures.
Require Import Program. 
From Equations Require Import Equations.  
From mathcomp Require Import all_ssreflect zify.
Require Import Relation_Definitions Setoid.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
Require Import ConstructiveEpsilon.
Require Import Numbers.BinNums.
Require Import PArith.BinPos.
From Containment Require Import  tactics utils regex pred modules constructiveEps enum extensional_partial.
Set Implicit Arguments.
Set Maximal Implicit Insertion.



Let inE := tactics.inE.


(*Module Type ContainerM.
Parameter (F : Type -> Type).
End ContainerM.*)

Module MyDSL (M : FModule).
Module CM := Constructive M.
Module PM := ContainsF M.
Module EM := ExtensionalPartial PM.
Import M CM EM.
(*Import M CM PM EM.*)
Inductive dsl (R: seq (@regex A * regex)) : regex -> regex -> Type := 
| shuffle A B C : dsl R ((A _+_ B) _+_ C) (A _+_ (B _+_ C))
| shuffleinv A B C : dsl R (A _+_ (B _+_ C)) ((A _+_ B) _+_ C)
| retag A B: dsl R (A _+_ B) (B _+_ A)
| untagL A : dsl R (Empt _+_ A) A
| untagLinv A: dsl R A  (Empt _+_ A)
| untag A : dsl R (A _+_ A)  A
| tagL A B : dsl R A  (A _+_ B )

| assoc A B C : dsl R ((A _;_ B) _;_ C)  (A _;_ (B _;_ C)) 
| associnv A B C : dsl R (A _;_ (B _;_ C))   ((A _;_ B) _;_ C)

| swap A :  dsl R (A _;_ Eps)  (Eps _;_ A) 
| swapinv A : dsl R(Eps _;_ A)  (A _;_ Eps) 

| proj A : dsl R (Eps _;_ A)  A 
| projinv A : dsl R A (Eps _;_ A) 

| abortR A : dsl R (A _;_ Empt)  Empt 
| abortRinv A : dsl R Empt   (A _;_ Empt) 

| abortL A : dsl R (Empt _;_ A)   Empt 
| abortLinv A : dsl R Empt    (Empt _;_ A)

| distL A B C : dsl R (A _;_ (B _+_ C))  ((A _;_ B) _+_ (A _;_ C))
| distLinv A B C : dsl R  ((A _;_ B) _+_ (A _;_ C)) (A _;_ (B _+_ C))

| distR A B C : dsl R ((A _+_ B) _;_ C)  ((A _;_ C) _+_ (B _;_ C))
| distRinv A B C : dsl R ((A _;_ C) _+_ (B _;_ C))   ((A _+_ B) _;_ C)

| wrap A : dsl R (Eps _+_ (A _;_ Star A))  (Star A)
| wrapinv A : dsl R (Star A)  (Eps _+_ (A _;_ Star A))

| drop A : dsl R  (Star (Eps _+_ A))  (Star A)
| dropinv A : dsl R (Star A)  (Star (Eps _+_ A))
| cid A : dsl R A A 

(*| ci_sym A B (H: A =R=B) : B =R=A*)
| ctrans A B C  : dsl R  A B ->  dsl R B C -> dsl R A C
| cplus A A' B B'  : dsl R A A'  -> dsl R B B' -> dsl R  (A _+_ B) (A' _+_ B')
| cseq A A' B B'  : dsl R A A' -> dsl R B B' ->  dsl R (A _;_ B) (A' _;_ B')
| cstar A B: dsl R  A B -> dsl R (Star A)  (Star B)
(*| rule_cfix r r' (p  : dsl R dsl) : dsl R r  r' ~> p[d (cfix p) .: dsl R var_dsl] ->  r  r' ~> (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dsl R ((Event a) _;_ A)  ((Event a) _;_ B)*)
(*| dsl_var a A B n : PTree.get n R = Some (A,B) -> dsl R ((Event a) _;_ A) ((Event a) _;_ B) *)
| dsl_var a A B :   (A,B) \in R -> dsl R (Event a _;_ A) (Event a _;_  B) 

(*without summation as that was due to productivity checker, not needed for inductive definition*)
| dsl_fix A B : dsl ((A,B):: R) A B -> dsl R A B.

(*| dsl_fix A B n : PTree.get n R = None -> dsl (PTree.set n (A,B) R) A B -> dsl R A B.*)
(**)
Notation "c0 < ⟨ R ⟩ = c1" := (dsl R c0 c1)(at level 63).


(*Module MyDec (M : FModule) <: DecidableType.
Import M.
Definition t := @regex A.
Definition eq (t0 t1 : t) := t0 = t1.
Lemma eq_equiv : Equivalence eq.
con; rewrite /eq; eauto. 
intro. intros. subst. done.
Qed.

Definition eq_dec : forall (x y : t), {x = y} + { x <> y}.
intros. destruct (eqVneq x y);eauto. constructor 2. apply/eqP. done.
Qed.
End MyDec.
*)

(*Print Orders.OrderedType.
Module MyOrderedType (M : FModule) <: Orders.OrderedType.
Import M.
Definition t := A

Module DSL_on (M : FModule) (X: Orders.OrderedType).
Module FM := MyPredF2 M.
Module MD := Make X.

(*Require Import MSets Arith.
Locate Nat_as_OT.
Locate  OrderedTypeEx.Nat_as_OT.
Check OrderedTypeEx.Nat_as_OT.

(* We can make a set out of an ordered type *)
Module S := Make Nat_as_OT

Section DSL.
Check PTree.tree.*)
(*Definition tree_add  (A' : Type) (r : PTRee.tree A) (k := *)
Print MD.
*)
Hint Constructors dsl : dsl.
Arguments shuffle {R A B C}.
Arguments shuffleinv {R A B C}.
Arguments retag {R A B}.
Arguments untagL {R A}.
Arguments untagLinv {R A}.
Arguments untag {R A}.
Arguments tagL {R A B}.
Arguments assoc {R A B C}.
Arguments associnv {R A B C}.
Arguments swap {R A}.
Arguments swapinv {R A}.
Arguments proj {R A}.
Arguments projinv {R A}.
Arguments abortR {R A}.
Arguments abortRinv {R A}.
Arguments abortL {R A}.
Arguments abortLinv {R A}.
Arguments distL {R A B C}.
Arguments distLinv {R A B C}.
Arguments distR {R A B C}.
Arguments distRinv {R A B C}.
Arguments wrap {R A}.
Arguments wrapinv {R A}.
Arguments drop {R A}.
Arguments dropinv {R A}.
Arguments cid {R A}.
Arguments ctrans {R A B C}.
Arguments cplus {R A A' B B'}.
Arguments cseq {R A A' B B'}.
Arguments cstar {R A B}.
Arguments dsl_var {R a A B}.
(*Arguments guard {R a A B}.*)
Arguments dsl_fix {R A B}.




Section CoinductiveDSL.
Inductive dslF (R: @regex A -> regex -> Type) : regex -> regex -> Type := 
| co_shuffle A B C : dslF R ((A _+_ B) _+_ C) (A _+_ (B _+_ C))
| co_shuffleinv A B C : dslF R (A _+_ (B _+_ C)) ((A _+_ B) _+_ C)
| co_retag A B: dslF R (A _+_ B) (B _+_ A)
| co_untagL A : dslF R (Empt _+_ A) A
| co_untagLinv A: dslF R A  (Empt _+_ A)
| co_untag A : dslF R (A _+_ A)  A
| co_tagL A B : dslF R A  (A _+_ B )

| co_assoc A B C : dslF R ((A _;_ B) _;_ C)  (A _;_ (B _;_ C)) 
| co_associnv A B C : dslF R (A _;_ (B _;_ C))   ((A _;_ B) _;_ C)

| co_swap A :  dslF R (A _;_ Eps)  (Eps _;_ A) 
| co_swapinv A : dslF R(Eps _;_ A)  (A _;_ Eps) 

| co_proj A : dslF R (Eps _;_ A)  A 
| co_projinv A : dslF R A (Eps _;_ A) 

| co_abortR A : dslF R (A _;_ Empt)  Empt 
| co_abortRinv A : dslF R Empt   (A _;_ Empt) 

| co_abortL A : dslF R (Empt _;_ A)   Empt 
| co_abortLinv A : dslF R Empt    (Empt _;_ A)

| co_distL A B C : dslF R (A _;_ (B _+_ C))  ((A _;_ B) _+_ (A _;_ C))
| co_distLinv A B C : dslF R  ((A _;_ B) _+_ (A _;_ C)) (A _;_ (B _+_ C))

| co_distR A B C : dslF R ((A _+_ B) _;_ C)  ((A _;_ C) _+_ (B _;_ C))
| co_distRinv A B C : dslF R ((A _;_ C) _+_ (B _;_ C))   ((A _+_ B) _;_ C)

| co_wrap A : dslF R (Eps _+_ (A _;_ Star A))  (Star A)
| co_wrapinv A : dslF R (Star A)  (Eps _+_ (A _;_ Star A))

| co_drop A : dslF R  (Star (Eps _+_ A))  (Star A)
| co_dropinv A : dslF R (Star A)  (Star (Eps _+_ A))
| co_cid A : dslF R A A 

(*| ci_sym A B (H: A =R=B) : B =R=A*)
| co_ctrans A B C  : dslF R  A B ->  dslF R B C -> dslF R A C
| co_cplus A A' B B'  : dslF R A A'  -> dslF R B B' -> dslF R  (A _+_ B) (A' _+_ B')
| co_cseq A A' B B'  : dslF R A A' -> dslF R B B' ->  dslF R (A _;_ B) (A' _;_ B')
| co_cstar A B: dslF R  A B -> dslF R (Star A)  (Star B)
(*| cfix r r' (p  : dslF R dslF) : dslF R r  r' p[d (cfix p) .: dslF R var_dslF] ->  r  r' (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dslF R ((Event a) _;_ A)  ((Event a) _;_ B)*)

(*We need this to be a sum because Coq disallows fix in cofix*)
| co_guard a A B  : R A B  -> dslF R ((Event a) _;_ A)  ((Event a) _;_ B).
(**)

(*parameterized gfp*)
Inductive sumboolT (A B : Type) : Type := 
 | leftT : A -> sumboolT A B
 | rightT : B -> sumboolT A B.
Definition bot2T (r0 r1 : @regex A) := False.
Definition rU {A B : Type} (R0 R1 : A -> B-> Type)  := fun r0 r1 => sumboolT (R0 r0 r1) (R1 r0 r1).

CoInductive dsl_co (R: @regex A -> @regex A -> Type) : regex -> regex -> Type := 
| Co_fold A B : (dslF (rU (dsl_co R) R)) A B -> dsl_co R A B.
Hint Constructors dsl_co.
End CoinductiveDSL.
Arguments co_shuffle {R A B C}.
Arguments co_shuffleinv {R A B C}.
Arguments co_retag {R A B}.
Arguments co_untagL {R A}.
Arguments co_untagLinv {R A}.
Arguments co_untag {R A}.
Arguments co_tagL {R A B}.
Arguments co_assoc {R A B C}.
Arguments co_associnv {R A B C}.
Arguments co_swap {R A}.
Arguments co_swapinv {R A}.
Arguments co_proj {R A}.
Arguments co_projinv {R A}.
Arguments co_abortR {R A}.
Arguments co_abortRinv {R A}.
Arguments co_abortL {R A}.
Arguments co_abortLinv {R A}.
Arguments co_distL {R A B C}.
Arguments co_distLinv {R A B C}.
Arguments co_distR {R A B C}.
Arguments co_distRinv {R A B C}.
Arguments co_wrap {R A}.
Arguments co_wrapinv {R A}.
Arguments co_drop {R A}.
Arguments co_dropinv {R A}.
Arguments co_cid {R A}.
Arguments co_ctrans {R A B C}.
Arguments co_cplus {R A A' B B'}.
Arguments co_cseq {R A A' B B'}.
Arguments co_cstar {R A B}.
Hint Constructors dslF.

Section DSL_Complete.

Ltac pp := intros;apply:proj2_sig.
Hint Constructors dsl. 

Lemma o_plus_l : forall c0 c1 R, (o (c0 _+_ c1)) <⟨R⟩= (o c0 _+_ o c1).
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto. 
Qed.

(*Lemma o_plus_l : forall c0 c1 R, (o (c0 _+_ c1)) <(R)= (o c0 _+_ o c1) ~> (proj_sig (o_plus_l c0 c1 R)).
Proof. pp. Qed.*)

Lemma o_plus_r : forall c0 c1 R, (o c0 _+_ o c1)  <⟨R⟩=  (o (c0 _+_ c1)).
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto. 
Qed.

(*Lemma o_plus_r : forall c0 c1 R, (o c0 _+_ o c1)  <⟨R⟩=  (o (c0 _+_ c1)) ~> (proj_sig (o_plus_r c0 c1 R)).
Proof. pp. Qed.*)


Lemma o_seq_l : forall c0 c1 R,  o (c0 _;_ c1) <⟨R⟩= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.

(*Lemma o_seq_l: forall c0 c1 R, o (c0 _;_ c1) <⟨R⟩= o c0 _;_ o c1 ~> (proj_sig (o_seq_l c0 c1 R)).
Proof. pp. Qed.*)

Lemma o_seq_r : forall c0 c1 R, o c0 _;_ o c1 <⟨R⟩=  o (c0 _;_ c1) .
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.

(*Lemma o_seq_r : forall c0 c1 R, o c0 _;_ o c1 <⟨R⟩=  o (c0 _;_ c1) ~> (proj_sig (o_seq_r c0 c1 R)).
Proof. pp. Qed.*)


Ltac bt H := apply:H.

Lemma ctrans1
     : forall c0 P c1 c2,
       c0 < ⟨P⟩= c1 -> c1 < ⟨P⟩= c2  ->  c0 <⟨P⟩= c2.
Proof.
intros. apply:ctrans;eauto.
Qed.

Lemma ctrans2
     : forall c0 P c1 c2,
       c1 < ⟨P⟩= c2 ->  c0 < ⟨P⟩= c1 -> c0 < ⟨P⟩= c2.
Proof.
intros. apply:ctrans;eauto.
Qed.

Lemma cplus1
     : forall c0 c0' P c1 c1',
       c0 < ⟨P⟩= c0' -> c1 < ⟨P⟩= c1' ->  c0 _+_ c1 < ⟨P⟩= c0' _+_ c1'. 
Proof.
intros. apply:cplus;eauto.
Qed.

Lemma cplus2
     : forall  c0 c0' P c1 c1',
       c1 < ⟨P⟩= c1' ->  c0 < ⟨P⟩= c0' ->   c0 _+_ c1 < ⟨P⟩= c0' _+_ c1'. 
Proof.
intros. apply:cplus;eauto.
Qed.

Lemma cseq1
     : forall c0 c0' c1 c1' P,
       c0 < ⟨P⟩= c0' ->
       c1 < ⟨P⟩= c1' ->  c0 _;_ c1 < ⟨P⟩= c0' _;_ c1'.
Proof. intros. apply:cseq;eauto.
Qed.

Lemma cseq2
     : forall c0 c0' c1 c1' P,
    c1 < ⟨P⟩= c1' ->
       c0 < ⟨P⟩= c0'  ->c0 _;_ c1 < ⟨P⟩= c0' _;_ c1'. 
Proof. intros. apply:cseq;eauto.
Qed.

Lemma cstar1
     : forall c0 c1 P,
      c0 < ⟨P⟩= c1 ->  Star c0 < ⟨P⟩= Star c1. 
Proof. intros. apply:cstar;eauto.
Qed.


Ltac lct1 := apply:ctrans1.
Ltac lct2 := apply:ctrans2.
Ltac lcid := bt cid.
Ltac lcp1 := apply:cplus1.
Ltac lcp2 := apply:cplus2.
Ltac lcs1 := apply:cseq1.
Ltac lcs2 := apply:cseq2.
Ltac lcst1 := apply:cstar1.
Print dsl.
Lemma split_plus_l : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) <⟨R⟩= \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a) .  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:shuffle.
lct2. apply:shuffleinv. lcp1. lcid.
lct2. lct2. apply:retag. apply:shuffleinv. 
lcp1. lcid. eauto.
Qed.

(*Lemma split_plus_l : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) <⟨R⟩= \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a) 
                                                                               (proj2_sig (split_plus_l R B l P P')).  
Proof. pp. Qed.*)

Lemma split_plus_r : forall R (B: eqType) l (P P' : B -> regex), 
 \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a)  <⟨R⟩=     \big[Plus/Empt]_(a <- l) (P a _+_ P' a) .  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:shuffle. lct2. apply:shuffleinv. lcp1.  lcid.
lct1. lct1. apply:retag. apply:shuffle. 
lcp1. lcid. eauto.
Qed.

(*Lemma split_plus_r : forall R (B: eqType) l (P P' : B -> regex), 
 \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a)  <⟨R⟩=     \big[Plus/Empt]_(a <- l) (P a _+_ P' a) (proj_sig (split_plus_r R B l P P')).  
Proof. pp. Qed.*)

Lemma factor_seq_l_l : forall R (B: eqType) l (P: B -> regex) c,   
\big[Plus/Empt]_(a <- l) (c _;_ P a) <⟨R⟩=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)) .
Proof.
move=> R B +P c. elim=>//=. econ. rewrite !big_nil //. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons //=.
lct2. apply:distLinv. lcp1. lcid. eauto. 
Qed.

(*Lemma factor_seq_l_l : forall R (B: eqType) l (P: B -> regex) c, 
\big[Plus/Empt]_(a <- l) (c _;_ P a) <⟨R⟩=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)) (proj_sig (factor_seq_l_l R B l P c)).
Proof. pp. Qed.*)


Lemma factor_seq_l_r : forall R (B: eqType) l (P: B -> regex) c,   
c _;_ (\big[Plus/Empt]_(a <- l) (P a)) 
<⟨R⟩=  
\big[Plus/Empt]_(a <- l) (c _;_ P a) 
.
Proof.
move=> R B +P c. elim=>//=. econ. rewrite !big_nil //. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons //=. 
lct1. apply:distL. lcp1. lcid. eauto. 
Qed.

(*Lemma factor_seq_l_r : forall R (B: eqType) l (P: B -> regex) c,
c _;_ (\big[Plus/Empt]_(a <- l) (P a)) 
<⟨R⟩=  
\big[Plus/Empt]_(a <- l) (c _;_ P a) 
(proj_sig (factor_seq_l_r R B l P c)).
Proof. pp. Qed.*)


Lemma factor_seq_r_l : forall R (B: eqType) l (P: B -> regex) c,  
\big[Plus/Empt]_(a <- l) (P a _;_ c) <⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c .
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct2. apply:distRinv. eauto. 
Qed.

(*Lemma factor_seq_r_l : forall R (B: eqType) l (P: B -> regex) c, 
\big[Plus/Empt]_(a <- l) (P a _;_ c) <⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c (proj_sig (factor_seq_r_l R B l P c)).
Proof. pp. Qed.*)

Lemma factor_seq_r_r : forall R (B: eqType) l (P: B -> regex) c,  
(\big[Plus/Empt]_(a <- l) (P a)) _;_ c 
<⟨R⟩= 
\big[Plus/Empt]_(a <- l) (P a _;_ c) . 
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:distR. eauto. 
Qed.

(*Lemma factor_seq_r_r : forall R (B: eqType) l (P: B -> regex) c, 
(\big[Plus/Empt]_(a <- l) (P a)) _;_ c 
<⟨R⟩= 
\big[Plus/Empt]_(a <- l) (P a _;_ c) (proj_sig (factor_seq_r_r R B l P c)). 
Proof. pp. Qed.*)



Lemma eps_c_r : forall r R,   r < ⟨R⟩= r _;_ Eps.
Proof.
intros. econ. lct2. apply:swapinv. eauto. done. done.
Qed.
(*Lemma eps_c_r : forall r R, r < ⟨R⟩= r _;_ Eps (proj_sig (eps_c_r r R)). 
Proof. pp. Qed.*)
Hint Resolve eps_c_r.

Lemma eps_c_l : forall r R,   r _;_ Eps < ⟨R⟩= r .
Proof.
intros. econ. lct1. apply:swap. eauto. eauto.
Qed.

(*Lemma eps_c_l : forall r R, r _;_ Eps < ⟨R⟩= r  (proj_sig (eps_c_l r R)).
Proof. pp. Qed.*)
Hint Resolve eps_c_l.
(*Lemma eps_c_l : forall r R,   Eps _;_ r < ⟨R⟩= r  d }.
Proof.
intros. econ. eauto. 
Qed.*)




Definition ex_coerce (l: seq A) (F0 F1 : A -> @regex A) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus_c : forall (l : seq A) F1 F2 R, ex_coerce l F1 F2 (dsl R) ->
   \big[Plus/Empt]_(i <- l) (F1 i) <⟨R⟩= \big[Plus/Empt]_(i <- l) (F2 i). 
Proof.
move=> + F1 F2 R. 
rewrite /ex_coerce. elim=>//.
move=> _. rewrite !big_nil//. 
move=> a l IH Hin. rewrite !big_cons /=. lcp1. apply:Hin. done.
eauto. 
Qed.

(*Add Parametric Morphism R : (Under_rel regex (c_ineq R)) with
signature (c_ineq R ==> c_ineq R ==> flip impl) as under_c_ineq. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''. apply/c_trans.  eauto. apply/c_trans. eauto. apply/c_sym. eauto.
Qed.*)

Lemma derive_seq_l : forall R a r r', a \ (r _;_ r') <⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') .
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /=. 
lcp1. lcid. eauto. 
rewrite /o Hcase /=.  eauto.
Qed.

(*Lemma derive_seq_l : forall R a r r', a \ (r _;_ r') <⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') (proj_sig (derive_seq_l R a r r')) .
Proof. pp. Qed.*)

Lemma derive_seq_r : forall R a r r', 
((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') 
 <⟨R⟩= 
a \ (r _;_ r')
.
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /=. 
lcp1. lcid. eauto. 

rewrite /o Hcase /=.  lct1. lct1. lcp1. lcid. apply:abortL. apply:retag. eauto. 
Qed.

(*Lemma derive_seq_r : forall R a r r', 
((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') 
 <⟨R⟩= 
a \ (r _;_ r')
(proj_sig (derive_seq_r R a r r')).
Proof. pp. Qed.*)


Lemma com_seq_o_l : forall R r r', o(r) _;_ r' <⟨R⟩= r' _;_ o(r) .
Proof.
intros. rewrite /o. case Heq:(nu _)=>//=. eauto.  
Qed.

(*Lemma com_seq_o_l : forall R r r',  o(r) _;_ r' <⟨R⟩= r' _;_ o(r) (proj_sig (com_seq_o_l R r r')).
Proof. pp. Qed.*)

Lemma com_seq_o_r : forall R r r', r' _;_ o(r)  <⟨R⟩=  o(r) _;_ r' .
Proof.
intros. rewrite /o. case Heq:(nu _)=>//=. eauto.  
Qed.

(*Lemma com_seq_o_r : forall R r r',  r' _;_ o(r)  <⟨R⟩=  o(r) _;_ r' (proj_sig (com_seq_o_r R r r')).
Proof. pp. Qed.*)


Lemma plus_empt_l : forall (A: eqType) R (l : seq A),  \big[Plus/Empt]_(a <- l) (Empt) <⟨R⟩ = Empt .
Proof.
move=> B R. elim=>//=. rewrite big_nil //. 
move=> a l IH. rewrite big_cons. lct2. apply:untag. lcp1. lcid. eauto.
Qed.

(*Lemma plus_empt_l : forall (A: eqType) R (l : seq A), \big[Plus/Empt]_(a <- l) (Empt) <⟨R⟩ = Empt (proj_sig (plus_empt_l A R l)).
Proof. pp. Qed.*)


Lemma big_event_notin_l R : forall l a, a \notin l ->   \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Empt . 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //. 
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite (negbTE Hneq).  move: (IH _ Hin). intros.
lct2. apply:untag. lcp1. eauto. eauto. 
Qed.

(*Lemma big_event_notin_l R : forall l a (H : a \notin l), \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Empt (proj_sig (big_event_notin_l R l a H)). 
Proof. pp. Qed.*)

Lemma big_event_notin_r R : forall l a, a \notin l -> Empt  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a))  . 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //. eauto.
Qed.

(*Lemma big_event_notin_r R : forall l a (H: a \notin l),  Empt  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a))  (proj_sig (big_event_notin_r R l a H)). 
Proof. pp. Qed.*)


Lemma empt_r_c : forall c R,  c _+_ Empt < ⟨R⟩= c .
Proof. eauto.
Qed.
(*Lemma empt_r_c : forall c R,  c _+_ Empt < ⟨R⟩= c (proj_sig (empt_r_c c R)).
Proof. pp. Qed.
Hint Resolve empt_r_c.*)

Lemma big_event_in_l R : forall l a, a \in l ->  \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Event a . 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. destruct (a0 == a) eqn:Heqn. move=>_.
move/eqP : Heqn=>Heq;subst.
rewrite big_cons eqxx //=. 
case Hcase: (a \in l). 
move: (IH _ Hcase). intros. lct2. apply:untag. lcp1. eauto. eauto. 
lct1. lcp1. apply:eps_c_l. apply:big_event_notin_l. 
rewrite Hcase. done.  eauto. 
simpl. intro. move: (IH _ H). intros. 
rewrite big_cons Heqn. lct1. lcp1. eauto.  eauto. eauto. 
Qed.

(*Lemma big_event_in_l R : forall l a (H : a \in l), \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Event a (proj_sig (big_event_in_l R l a H)). 
Proof. pp. Qed.*)

Lemma big_event_in_r R : forall l a, a \in l -> Event a  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) . 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. destruct (a0 == a) eqn:Heqn. move=>_.
move/eqP : Heqn=>Heq;subst.
rewrite big_cons eqxx //=. 
case Hcase: (a \in l). 
move: (IH _ Hcase). intros. lct2.  apply:tagL. eauto. 
have: a \notin l. by lia.
move=>HH. lct2.  apply:tagL. eauto. 
simpl. move=>HH.
move: (IH _ HH). intros. rewrite big_cons /= Heqn.
lct2. apply:retag. lct2. apply:tagL. eauto. 
Qed.

(*Lemma big_event_in_r R : forall l a (H : a \in l), Event a  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) (proj_sig (big_event_in_r R l a H)). 
Proof.
pp. 
Qed.*)

(*Uses drop!*)
Lemma star_o_l : forall R c c', Star (o (c) _+_ c') <⟨R⟩ = Star c' .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.
(*Lemma star_o_l : forall R c c', Star (o (c) _+_ c') <⟨R⟩ = Star c' (proj_sig (star_o_l R c c')).
Proof. pp. Qed.*)

Lemma star_o_r : forall R c c', Star c' <⟨R⟩ =  Star (o (c) _+_ c') .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.

(*Lemma star_o_r : forall R c c', Star c' <⟨R⟩ =  Star (o (c) _+_ c') (proj_sig (star_o_r R c c')).
Proof. pp. Qed.*)

Lemma derive_unfold_coerce : forall c, dsl nil c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c))  *
                                   dsl nil (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c.
Proof.
elim;try solve [eauto].
- con. eauto. rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 
- con. eauto. rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 

- move=> s. con.
 *  rewrite /o /=. lct2. apply:retag. lct2. apply:tagL. 
    apply:big_event_in_r. rewrite mem_index_enum //. 
 *  rewrite /o /=. lct1. apply:untagL. apply:big_event_in_l. rewrite mem_index_enum //. 
- move=> r0 [] Hd0 Hd0' r1 [] Hd1 Hd1'. econ.
(*[] d1 Hd1 [] d1' Hd1'. econ.*)
 * 
   lct1. lcp1. apply:Hd0. apply:Hd1. 
   lct1. apply:shuffle. lct2. lcp1. apply: o_plus_r. lcid. 
   lct2. apply:shuffleinv. lcp1. lcid. 
   lct1. lct1. apply:retag. apply:shuffle. 
   lcp1. lcid. simpl. 
   lct2. apply:eq_big_plus_c. intro. intros. apply:distLinv.
   lct2. lct2.  apply:split_plus_r.  apply:retag. 
   lcp1. lcid. lcid. 
 * 
   lct2. lcp2. apply:Hd1'. apply:Hd0'. 
   lct2. apply:shuffleinv. lct1. lcp1. apply: o_plus_l. lcid. 
   lct1. apply:shuffle. lcp1. lcid. simpl. 
   lct1. lcp1. lcid. lct1. apply:eq_big_plus_c. intro. intros. apply:distL. 
   apply split_plus_l. 
   lct1. lct1. apply:retag. apply:shuffle. lcp1. lcid.
   lct1. apply:retag. eauto. 
- move=> r0 [] Hd0 Hd0' r1 [] Hd1 Hd1'. econ.

(*- move=> r0 [] [] d0 Hd0 [] d0' Hd0' r1 [] [] d1 Hd1 [] d1' Hd1'. econ.*)
  * 
    lct2. lcp1. apply: o_seq_r. 
    lct2. apply: eq_big_plus_c. intro. intros. lct2. lcs1. lcid. apply:derive_seq_r.
    lct2. apply:distLinv. lct2. lcp1. lct2. apply:assoc. lcs1. lcid. apply:Hd1'.
    lct2. lcs1. lcid. apply:com_seq_o_r. apply:assoc. lcid.
    lct2. apply: split_plus_r. lct2. lcp1.
    lct2. apply:factor_seq_r_r.  apply:distLinv. apply: factor_seq_r_r. lcid.
    lct1. lcs1. apply: Hd0. apply: Hd1.
    lct1. apply:distR.
    lct1. lcp1. apply:distL. apply:distL.
    lct1. apply:shuffle. lcp1. lcid.
    lct2. apply:retag. lcp1. apply:com_seq_o_l.
    lcp1. eauto. eauto. 
  * econ. 
    lct1. lcp1. apply: o_seq_l. 
    lct1. apply: eq_big_plus_c. intro. intros. lct1. lcs1. lcid. apply:derive_seq_l.
    lct1. apply:distL. lct1. lcp1. lct1. apply:associnv. lcs1. lcid. apply:Hd1.
    lct1. lcs1. lcid. apply:com_seq_o_l. apply:associnv. lcid.
    lct1. apply: split_plus_l. lct1. lcp1.
    lct1. apply:factor_seq_r_l.  apply:distL. apply: factor_seq_r_l. lcid.
    lct2. lcs1. apply: Hd0'. apply: Hd1'.
    lct2. apply:distRinv.
    lct2. lcp2. apply:distLinv. apply:distLinv.
    lct2. apply:shuffleinv. lcp1. lcid.
    lct2. apply:retag. lcp1. lcid. apply:com_seq_o_r. done.
    
- move=> r0 [] Hd Hd'. con.  
  * lct2. lcp1. lcid. simpl. lct2. 
    apply:eq_big_plus_c. intro. intros. lct2. apply:assoc. lcs1. lcid.
    lcst1. apply/Hd'. 
    apply:factor_seq_r_r. 
    lct1. lct1. lcst1. apply: Hd. apply: star_o_l.
    rewrite {1}/o /=.
    lct2. lcp1. lcid. lcs1. lcid. apply: star_o_r. eauto.  
  *  lct1. lcp1. lcid. simpl. lct1. 
    apply:eq_big_plus_c. intro. intros. lct1. apply:associnv. lcs1. lcid.
    lcst1. apply/Hd. 
    apply:factor_seq_r_l. 
    lct2. lct2. lcst1. apply: Hd'. apply: star_o_r.
    rewrite {1}/o /=.
    lct1. lcp1. lcid. lcs1. lcid. apply: star_o_l. eauto.  
Qed.



Lemma derive_unfold_coerce_l : forall c,  dsl nil c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)). 
Proof.
intros. destruct (derive_unfold_coerce c). done.
Qed.
(*Lemma derive_unfold_coerce_l : forall c R, c_ineq R c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) (proj_sig (derive_unfold_coerce_l_aux c)). 
Proof. intros. apply/c_ineq_gen_mon. pp. done.
Qed.*)

Lemma derive_unfold_coerce_r : forall c, dsl nil (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c.
Proof.
intros. destruct (derive_unfold_coerce c). done.
Qed.


(*Lemma derive_unfold_coerce_r : forall R c, c_ineq R (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c (proj_sig (derive_unfold_coerce_r_aux c)).
Proof. intros. apply/c_ineq_gen_mon. pp. done.
Qed.*)

(*Definition decomp_l c := proj_sig (derive_unfold_coerce_l_aux c).
Definition decomp_r c := proj_sig (derive_unfold_coerce_r_aux c).*)

(*Lemma decomp_l : forall c, INEQ c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) (proj_sig (derive_unfold_coerce_l_aux INEQ c)). 
Proof. intros. pfold. apply:c_ineq_gen_mon. apply:derive_unfold_coerce_l. eauto.
Qed.

Lemma decomp_r : forall c, INEQ (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c (proj_sig (derive_unfold_coerce_r_aux INEQ c)). 
Proof. intros. pfold. apply:c_ineq_gen_mon. apply:derive_unfold_coerce_r. eauto.
Qed.*)

(*Definition sum_dsl  (F : A -> dsl) := (\big[cplus/cid]_(a : A) (guard (F a))).*)
(*Definition decomp_rec c R := 
cfix (ctrans (decomp_l R) (sum_dsl (fun a => decomp_rec (a \ c) R)))*)

(*Lemma big_shape: forall c, \big[Plus/Empt]_a (Event a _;_ a \ c) = \big[Plus/Empt]_(i <- map (fun a => (a,a\c)) (index_enum A)) (Event i.1 _;_  i.2).
Proof.
move=> c. move Heq: (index_enum _)=>ef. clear Heq.
elim: ef. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons /=. f_equal. done.
Qed.*)

(*Lemma nu_imp_coerce_aux : forall r0 r1 r2 r3 d R, (nu r0 -> nu r1) -> r2 <⟨R⟩= r3 d ->  ' | o (r0) _+_ r2 <⟨R⟩= o(r1) _+_ r3 d'}.
Proof.
intros. destruct (nu r0) eqn:Heqn. rewrite /o Heqn H //. econ. lcp1. lcid. eauto.
rewrite /o Heqn.
destruct (nu r1). econ. 
lct1. apply:untagL. lct2. apply:retag. eauto.
econ. 
lct1. apply:untagL. lct2. apply:retag. eauto.
Qed.

Lemma nu_imp_coerce : forall r0 r1 r2 r3 d R (H : (nu r0 -> nu r1)) (H' : r2 <⟨R⟩= r3 d),  o (r0) _+_ r2 <⟨R⟩= o(r1) _+_ r3 (proj_sig (nu_imp_coerce_aux r0 r1 H H')).
Proof. pp. Qed.*)

Lemma nu_imp_coerce_aux : forall r0 r1, (nu r0 -> nu r1) ->  o r0 <⟨nil⟩= o r1. 
Proof.
intros. destruct (nu r0) eqn:Heqn. rewrite /o Heqn H //. econ. lcid. 
rewrite /o Heqn.
destruct (nu r1). econ.
lct2. apply:untagL.
apply:tagL.
eauto. done.
Qed.

(*Lemma nu_imp_coerce : forall r0 r1 (H : nu r0 -> nu r1),  o r0 <⟨PTree.empty _⟩= o r1 ( proj_sig (nu_imp_coerce_aux r0 r1 H)). 
Proof. pp. Qed.*)


(*Lemma nu_imp_coerce : forall r0 r1 r2 r3 d R (H : (nu r0 -> nu r1)) (H' : r2 <⟨R⟩= r3 d),  o (r0) _+_ r2 <⟨R⟩= o(r1) _+_ r3 (proj_sig (nu_imp_coerce_aux r0 r1 H H')).
Proof. pp. Qed.*)
Lemma big_plus_coerce : forall (l : seq A) F0 F1 R, (forall a, a \in l ->  (F0 a,F1 a) \in R) ->
 (\big[Plus/Empt]_(a <- l) (Event a _;_ F0 a)) <⟨R⟩=  (\big[Plus/Empt]_(a <- l) (Event a _;_ F1 a)).  
Proof.
elim;ssa. rewrite !big_nil. eauto.
rewrite !big_cons. lcp1.  
have: a \in a::l. done. move/H. 
ssa. apply X. eauto.
Qed.

Lemma Empt_Eps : forall L, Empt < ⟨ L ⟩ = Eps.
Proof.
intros. lct1. apply:tagL. 2: { lct1. apply:retag. eauto. } 
Qed.
Hint Resolve Empt_Eps.

Lemma Empt_r : forall L r, Empt < ⟨ L ⟩ = r.
Proof.
intros. lct1. apply:tagL. 2: { lct1. apply:retag. eauto. } 
Qed.


Lemma o_lP : forall l l' L, (has nu l -> has nu l') ->  o_l l <⟨ L ⟩ = o_l l'.
Proof.
intros. rewrite /o_l. case_if;ssa. 
rewrite H //. case_if=>//.
Qed.

Lemma nu_false : nu (\big[Plus/Empt]_(a : A) (Event a _;_ Empt)) = false.
Proof.
move: (index_enum A)=> l.
elim: l;ssa.
rewrite !big_nil. ssa.
rewrite !big_cons. ssa.
Qed.

Lemma nu_has : forall (l : @pder A), nu (\big[Plus/Empt]_(i <- l) i) = has nu l.
Proof.
elim;ssa. rewrite !big_nil. done.
rewrite !big_cons. ssa. f_equal. done.
Qed.

Lemma c_eq_cat1 : forall l0 l1 L,  \big[Plus/Empt]_(i <- l0 ++ l1) i <⟨L⟩=  \big[Plus/Empt]_(i <- l0) i _+_  \big[Plus/Empt]_(i <- l1) i.
Proof.
elim;ssa.
rewrite !big_nil //. 
rewrite !big_cons. lct2.  apply:shuffleinv. lcp1. done.  done.
Qed.

Lemma c_eq_cat2 : forall l0 l1 L,  \big[Plus/Empt]_(i <- l0) i _+_  \big[Plus/Empt]_(i <- l1) i <⟨L⟩=   \big[Plus/Empt]_(i <- l0 ++ l1) i . 
Proof.
elim;ssa.
rewrite !big_nil //. 
rewrite !big_cons. lct1.  apply:shuffle. lcp1. done.  done.
Qed.



Lemma c_eq_derive_pd_l1 : forall c L a, a \ c <⟨ L ⟩ = \big[Plus/Empt]_(i <- pd a c) i.
Proof.
elim;ssa; try solve [ rewrite !big_nil //=].
case_if. norm_eqs. rewrite eqxx //= !big_cons big_nil.  auto.
rewrite eq_sym H big_nil //=.
lct2. apply:c_eq_cat2.
lcp1. done. done.
case_if. lct2. apply:c_eq_cat2. lcp1. rewrite map_big_plus.
lct2. apply:factor_seq_r_r. apply:cseq. done. done. done.
rewrite map_big_plus.
lct2. apply:factor_seq_r_r. apply:cseq. done. done. 
rewrite map_big_plus.
lct2. apply:factor_seq_r_r. apply:cseq. done. done. 
Qed.

Lemma c_eq_derive_pd_l2 : forall c L a, \big[Plus/Empt]_(i <- pd a c) i <⟨ L ⟩ =  a \ c.
Proof.
elim;ssa; try solve [ rewrite !big_nil //=].
case_if. norm_eqs. rewrite eqxx //= !big_cons big_nil. lct1. apply retag. eauto.
rewrite eq_sym H big_nil //=.
lct1. apply:c_eq_cat1.
lcp1. done. done.
case_if. lct1. apply:c_eq_cat1. lcp1. rewrite map_big_plus.
lct1. apply:factor_seq_r_l. apply:cseq. done. done. done.
rewrite map_big_plus.
lct1. apply:factor_seq_r_l. apply:cseq. done. done. 
rewrite map_big_plus.
lct1. apply:factor_seq_r_l. apply:cseq. done. done. 
Qed.


Lemma c_eq_undup1 : forall l L,  \big[Plus/Empt]_(i <- (undup l)) i <⟨L⟩=  \big[Plus/Empt]_(i <- l) i.
Proof.
elim;ssa.
case_if.  rewrite !big_cons. 
lct2. lcp1. lcid. apply:X. clear X.
elim: l a H;ssa. 
rewrite !inE in H. destruct (eqVneq a0 a).   subst. ssa.

case_if. eauto. rewrite /= !big_cons.
apply:ctrans2. apply:ctrans2. apply:shuffle. lcp1. apply:tagL. lcid.  
lcp1. done. done.
ssa.
case_if=>//. lct2. apply:retag. eauto.
rewrite !big_cons. lct2. apply:retag. eauto.
rewrite !big_cons. eauto.
Qed.

Lemma c_eq_undup2 : forall l L, \big[Plus/Empt]_(i <- l) i  <⟨L⟩=  \big[Plus/Empt]_(i <- (undup l)) i.  
Proof.
elim;ssa. rewrite !big_cons.
case_if.  lct2. apply:X.
clear X.
elim: l a H;ssa. 
rewrite !inE in H. 
destruct (eqVneq a0 a). subst. rewrite !big_cons.
lct1. apply shuffleinv. lcp1. eauto. eauto. 
simpl. rewrite !big_cons. lct1. apply shuffleinv.
lct1. lcp1. apply retag. lcid. lct1. apply shuffle. lcp1. lcid. apply:X. done.
rewrite !big_cons. eauto.
Qed.

Lemma big_plus1 : forall a F, F a <⟨nil⟩= a \ \big[Plus/Empt]_a0 (Event a0 _;_ F a0).
Proof.
move=> a.
have: a \in index_enum A by done. 
move : (index_enum A)=>l.
elim: l;ssa. rewrite !big_cons. rewrite !inE in H. simpl.
destruct (eqVneq a a0). subst. 
lct2. lcp1. apply:projinv.  lcid. eauto.
lct1. apply X. ssa. eauto.
Qed.

Lemma big_event_notin_lF R : forall (l : seq A) a (F : A -> regex), a \notin l ->   a \ \big[Plus/Empt]_(i <- l) (Event i _;_ (F i)) <⟨R⟩= Empt . 
Proof.
elim=>//=;ssa. rewrite !big_nil //.
rewrite  !inE in H.  ssa.
rewrite !big_cons. ssa.  rewrite eq_sym (negbTE H0). 
lct1. lcp1. instantiate (1:= Empt). eauto. apply:X. done. eauto.
Qed.

Lemma big_plus2 : forall a F, a \ \big[Plus/Empt]_a0 (Event a0 _;_ F a0) <⟨nil⟩=  F a.
Proof.
move=> a.
have: a \in index_enum A by done. 
move : (index_enum A)=>l.
elim: l;ssa. rewrite !big_cons. rewrite !inE in H. 
destruct (eqVneq a a0). subst. rewrite /= eqxx. 
lct1. lcp1. apply proj. lcid. 
destruct (a0 \in l) eqn:Heqn. lct2. apply untag.  
lct2. lcp1.  apply X.  done. lcid. eauto. 
lct1. lcp1. lcid. apply:big_event_notin_lF. rewrite Heqn. done.
eauto.

simpl. rewrite eq_sym (negbTE i).
lct1. lcp1. instantiate (1:= Empt). eauto. apply:X. ssa.
eauto.
Qed.


Definition is_sub_bool {A : eqType} (l0 l1 : seq A) := all (fun x => x \in l1) l0. 
Lemma is_subP : forall (A : eqType) (l0 l1 : seq A), is_sub l0 l1 <-> is_sub_bool l0 l1.
Proof.
intros. split. 
rewrite /is_sub. intros. apply/allP. intro. eauto.
move/allP.  eauto.
Qed.

Lemma dsl_mon : forall l l' E F, dsl l E F -> is_sub_bool l l' ->  dsl l' E F.
Proof.
move=> l l' E F p. 
elim: p l';auto with dsl;simpl;intros.
apply:ctrans. eauto. eauto.
apply:dsl_var. move/is_subP : H=>Hsub. apply Hsub. done.
apply:dsl_fix. apply:X. ssa.
apply/is_subP. move/is_subP : H.
intro. intro. move/H. rewrite !inE. move=>->//. lia.
Defined.





Lemma decomp_p1_aux : forall l ,  \big[Plus/Empt]_(i <- l) i <⟨nil⟩= (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof. 
intros. 
rewrite /pd_l. 
suff:   \big[Plus/Empt]_(i <- l) i < ⟨ [::] ⟩ =
  o_l l _+_ \big[Plus/Empt]_a (Event a _;_ \big[Plus/Empt]_(i <- (flatten [seq pd a i | i <- l])) i).
intros. lct1. apply:X. lcp1. lcid.
apply eq_big_plus_c. intro. ssa. lcs1. lcid. 
lct2. apply c_eq_undup2. done.
lct1. apply:derive_unfold_coerce_l. 
lct2. apply:derive_unfold_coerce_r.
lcp1. 
rewrite /o_l /o. rewrite nu_has. 
destruct (has nu _) eqn:Heqn. simpl. done. simpl. eauto.

apply/eq_big_plus_c.
intro. ssa. apply:cseq. done.
lct1. apply/tagL. 
2: { lct1. apply/retag. lcp1. lcid. rewrite !big_derive. 
     lct2. apply:big_plus1. 
     elim: l;ssa. 
     rewrite !big_cons. lct2. apply c_eq_cat2. lcp1. 
     apply c_eq_derive_pd_l1. done. } 
Qed.

Lemma decomp_p1 : forall l L ,  \big[Plus/Empt]_(i <- l) i <⟨L⟩= (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof.
intros. apply/dsl_mon. apply/decomp_p1_aux. eauto.
Qed.

Lemma nu_plus : forall (A' : Type)l (F : A' -> @regex A), nu(\big[Plus/Empt]_(a <- l) (F a)) = has (fun x => nu (F x)) l.
Proof.
move=> A'.
elim;ssa. rewrite !big_nil. ssa.
rewrite !big_cons. simpl. f_equal. done.
Qed.

Lemma has_xpred0 : forall (A : Type) (l : seq A), has xpred0 l = false.
Proof.
move=> A. elim;ssa.
Qed.


Lemma decomp_p2_aux : forall l,  (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨nil⟩=  \big[Plus/Empt]_(i <- l) i.
Proof. 
intros. 
rewrite /pd_l. 
suff: 
  o_l l _+_ \big[Plus/Empt]_a (Event a _;_ \big[Plus/Empt]_(i <- (flatten [seq pd a i | i <- l])) i)  < ⟨ [::] ⟩ =  \big[Plus/Empt]_(i <- l) i.
intros. lct2. apply:X. lcp1. lcid.
apply eq_big_plus_c. intro. ssa. lcs1. lcid. 
lct2. apply c_eq_undup1. done.
lct1. apply:derive_unfold_coerce_l. 
lct2. apply:derive_unfold_coerce_r.
lcp1. 
rewrite /o_l /o. rewrite nu_has. 
destruct (has nu _) eqn:Heqn. simpl. done. simpl. 
rewrite nu_plus. simpl. rewrite has_xpred0. done.
apply/eq_big_plus_c.
intro. ssa. apply:cseq. done.
have: a \ o_l l = Empt. 
rewrite /o_l. case_if;ssa.
move=>->. lct1. apply untagL.
rewrite !big_derive. 
lct1. apply:big_plus2. 
     elim: l;ssa. 
     rewrite !big_cons. lct1. apply c_eq_cat1. lcp1. 
     apply c_eq_derive_pd_l2. done. 
Qed.

Lemma decomp_p2 : forall l L,  (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨L⟩=  \big[Plus/Empt]_(i <- l) i.
Proof.
intros. apply/dsl_mon. apply/decomp_p2_aux. eauto.
Qed.

(*To avoid universe inconsistency we create a type similar to sumbool*)

Check @reachable.

(*Parameter  (V : @vType A) (l : @nType A) (H : D_bisim V l)  (Hnot: l\notin V). 
Check (D_bisim_proj H Hnot).*)
(*l\notin V -> reachable PM.Pb H = *)
(*                                                              (PM.Pb l.1 l.2) && (allP (fun (a : A) => @reachable _ (l::V) (pair_pd_l a l) PM.Pb (D_bisim_proj H a)) (index_enum A)).
*)

Lemma reachable_simp : forall V l (H : D_bisim V l) (Hnot: l\notin V), reachable PM.Pb H = 
                                                              (PM.Pb l.1 l.2) && (all (fun (a : A) => reachable  PM.Pb (D_bisim_proj H Hnot a)) (index_enum A)).
Proof.
intros. destruct H.  ssa. exfalso.
rewrite i in Hnot. done. ssa. rewrite (negbTE Hnot) /=. ssa.
Qed.

Fixpoint proof_irrel  V l (H H' : D_bisim V l) {struct H} : reachable PM.Pb H = reachable PM.Pb H'.
Proof.
refine (
match H in D_bisim V' l' return V' = V -> l' = l -> reachable PM.Pb H = reachable PM.Pb H' with 
| Db_stop x y z => fun HQ HQ' =>_
| Db_next x y z a b => fun HQ HQ'=> _
end Logic.eq_refl Logic.eq_refl).
ssa;subst.  destruct H'; ssa.
destruct (Utils.dec _). done. f_equal. 
apply/eq_in_all. intro. ssa.
destruct (Utils.dec _). done. 
f_equal. apply/eq_in_all.  intro. ssa. subst.
destruct H'. exfalso. rewrite i in z. ssa.
ssa.
destruct (Utils.dec _). done. 
f_equal. apply/eq_in_all. intro. ssa.
Qed.

Fixpoint EQ_complete_aux p (V : seq (@pder A * @pder A)) (H : D_bisim V p) {struct H} : forall (L : seq (@regex A * @regex A)),
    (forall x y, (x,y) \in V ->  (\big[Plus/Empt]_(i <- x) i, \big[Plus/Empt]_(i <- y) i) \in L) -> 
                                                         reachable PM.Pb H -> 
                                                        sumboolT (((\big[Plus/Empt]_(i <- p.1) i), (\big[Plus/Empt]_(i <- p.2) i)) \in L)
                                                                 ((\big[Plus/Empt]_(i <- p.1) i) <⟨L⟩= (\big[Plus/Empt]_(i <- p.2) i)).
simpl. ssa.
destruct (p \in V) eqn:Heqn. left.
apply/H0. de p.
have: p \notin V. lia.
move=>Hnot.
move: (D_bisim_proj H Hnot)=>HD. clear Heqn.
right.
apply dsl_fix.
apply:ctrans. apply:decomp_p1. 
apply:ctrans. 2: {  apply:decomp_p2. } 
move: H1.
rewrite reachable_simp //. ssa.
apply:cplus. apply:(@dsl_mon nil)=>//. apply:o_lP.  move/implyP:H2=>Himp. apply/Himp.
destruct p. ssa.
move  HeqL':  ((\big[Plus/Empt]_(i <- p) i, \big[Plus/Empt]_(i <- p0) i) :: L) => L'.
suff: forall a, Event a _;_  \big[Plus/Empt]_(i <- pd_l a p) i <⟨L'⟩= Event a _;_  \big[Plus/Empt]_(i <- pd_l a p0) i.
intros. clear H H2 H3 HeqL'.
move: X.
move:(index_enum A)=> lA.
elim: lA. 
ssa. rewrite !big_nil. done.
ssa. rewrite !big_cons. lcp1. done.
apply/X. done. 
intros. 
move Heq : ( \big[Plus/Empt]_(i <- pd_l a p) i) => r0.
move Heq2 : ( \big[Plus/Empt]_(i <- pd_l a p0) i) => r1.
suff:    
sumboolT ((r0,r1) \in L') (r0 <⟨L'⟩=r1).
intros. destruct X. apply:dsl_var. done.
apply:cseq. done. done. 
move:(EQ_complete_aux _ _ (HD a))=>//= HH. 
subst. apply HH. intros.
rewrite !inE in H1. de (orP H1). norm_eqs. inv H4. rewrite eqxx //. auto.
erewrite proof_irrel.
apply (allP H3). done.
Qed.



Lemma bisim_c_eq : forall l l', reachable_wrap l l' PM.Pb ->  (\big[Plus/Empt]_(i <- l) i) <⟨nil⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. apply (@EQ_complete_aux _ _ _ nil) in H. destruct H. done. simpl in d.
lct1. apply c_eq_undup2. 
lct2. apply c_eq_undup1. done. 
ssa.
Qed.

Lemma equiv_r_plus : forall (c0 c1 : @regex A), contains_r c0 c1 -> contains_r (\big[Plus/Empt]_(i <- c0::nil) i)  (\big[Plus/Empt]_(i <- c1::nil) i).
Proof.
intros. intro. ssa. move: H0. rewrite !big_cons !big_nil. intros. inv H0;eauto. con. apply/H. done.
inv H3.
Qed.

(*Lemma c_eq_soundness_alternative_proof : forall (c0 c1 : regex), c0 <⟨nil⟩= c1 ->  equiv_r c0 c1.
Proof. move=> c0 c1. move/c_eq_ind_coind. move/bisim_soundness. move/equivP=>//.
Qed.*)

Lemma c_eq_completeness : forall (c0 c1 : regex), contains_r c0 c1 -> c0 <⟨nil⟩= c1.
Proof. move=> c0 c1. move/equiv_r_plus. move/Bisim_co_ind. move/bisim_complete.
move/bisim_c_eq. rewrite !big_cons !big_nil. eauto.
Qed.
