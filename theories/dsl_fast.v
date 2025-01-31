From HB Require Import structures.
Require Import Program. 
From mathcomp Require Import all_ssreflect zify.
Require Import Relation_Definitions Setoid.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
Require Import ConstructiveEpsilon.
Require Import Numbers.BinNums.
Require Import PArith.BinPos.
From Containment Require Import  tactics utils regex pTree enum. (* constructiveEps enum (*dsl_module*) extensional_partial.*)
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Let inE := tactics.inE.


(*Module IndDSL (M : FModule).*)
Section DSL.
Variable (Af : finType).
(*Module PM := ContainsF M.
Module CM := Constructive M.
Module EM := ExtensionalPartial PM.
Import M CM EM.*)

Inductive dsl (R: seq (@regex Af * regex)) : regex -> regex -> Type := 
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

| drop A B : dsl R A (Eps _+_ B) -> dsl R (Star A)  (Eps _+_ B _;_ Star ( A))
(*| dropinv A B : dsl R (Eps _+_ B) A -> dsl R  (Eps _+_ B _;_ Star ( A)) (Star A) *)
| cid A : dsl R A A 

(*| ci_sym A B (H: A =R=B) : B =R=A*)
| ctrans A B C  : dsl R  A B ->  dsl R B C -> dsl R A C
| cplus A A' B B'  : dsl R A A'  -> dsl R B B' -> dsl R  (A _+_ B) (A' _+_ B')
| cseq A A' B B'  : dsl R A A' -> dsl R B B' ->  dsl R (A _;_ B) (A' _;_ B')
(*| cstar A B: dsl R  A B -> dsl R (Star A)  (Star B)*)
(*| rule_cfix r r' (p  : dsl R dsl) : dsl R r  r' ~> p[d (cfix p) .: dsl R var_dsl] ->  r  r' ~> (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dsl R ((Event a) _;_ A)  ((Event a) _;_ B)*)
(*| dsl_var a A B n : PTree.get n R = Some (A,B) -> dsl R ((Event a) _;_ A) ((Event a) _;_ B) *)
| dsl_var a A B :   (A,B) \in R -> dsl R (Event a _;_ A) (Event a _;_  B) 
| dsl_fix A B : dsl ((A,B):: R) A B -> dsl R A B.
Notation "c0 < ⟨ R ⟩ = c1" := (dsl R c0 c1)(at level 63).

Lemma dropinv R A B : dsl R (Eps _+_ B) A -> dsl R  (Eps _+_ B _;_ Star ( A)) (Star A). 
Proof.
intros. apply:ctrans. apply:cplus. apply:cid. apply:cseq.
apply:ctrans. apply:tagL. apply: Eps. 
apply:ctrans. apply:retag.  apply:X. apply:cid.
apply:wrap.
Qed.

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
(*Arguments projinv {R A}.*)
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
Arguments drop {R A B}.
Arguments dropinv {R A B}.
Arguments cid {R A}.
Arguments ctrans {R A B C}.
Arguments cplus {R A A' B B'}.
Arguments cseq {R A A' B B'}.
(*Arguments cstar {R A B}.*)
Arguments dsl_var {R a A B}.
(*Arguments guard {R a A B}.*)
Arguments dsl_fix {R A B}.
Hint Constructors dsl.


Fixpoint interp l r0 r1 (p : dsl l r0 r1) (T : pTree r0) 
         (f : forall x y,  (x,y) \in l -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) {struct p}:
  post r1 T. 
refine(
match p in dsl _ x y return r0 = x -> r1 = y -> post r1 T  with
| dsl_fix r0 r1 p0 => fun HQ HQ' => _ (*Do at least one case to force coq to destruct *)
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
all:clear p;intros;subst.
(*move: T f. apply:pTree_case=>//. intros. inv_eq. move: f. simpl. rewrite <- eq_regex. Set Printing All.
 clear_eq.*) 
dp T f.
dp p f.
exists (p_inl p)=>//=.  
exists (p_inr (p_inl p))=>//=.
exists (p_inr (p_inr p))=>//=.

dp T f.
exists (p_inl (p_inl p))=>//.
dp p f.
exists (p_inl (p_inr p))=>//.
exists (p_inr p)=>//.

dp T f.
exists (p_inr p)=>//.
exists (p_inl p)=>//=.

dp T f.
dp p f.
exists p=>//.
exists (p_inr T)=>//.

dp T f.
exists p=>//.
exists p=>//.

exists (p_inl T)=>//.

dp T f.
dp p0 f.
exists (p_pair p0 (p_pair p2 p1))=>//=. ssa. lia. rewrite catA //.

dp T f.
dp p1 f.
exists (p_pair (p_pair p0 p1) p2)=>//=. ssa. lia. rewrite catA //.

dp T f.
dp p1 f.
exists (p_pair p_tt p0)=>//=. ssa. lia. rewrite cats0 //.

dp T f.
dp p0 f.
exists (p_pair p1 p_tt)=>//=. ssa. lia. rewrite cats0 //.

dp T f.
dp p0 f.
exists p1=>//=.

exists (p_pair p_tt T)=>//=. 

dp T f.
dp p1 f.

dp T f.

dp T f. dp p0 f.
dp T f.

dp T f. dp p1 f.
exists (p_inl (p_pair p0 p))=>//=.
exists (p_inr (p_pair p0 p))=>//=.

dp T f. dp p f.
exists (p_pair p0 (p_inl p1))=>//=.
dp p f.
exists (p_pair  p0 (p_inr p1))=>//=.

dp T f. dp p0 f.
exists (p_inl (p_pair p p1))=>//=.
exists (p_inr (p_pair p p1))=>//=.

dp T f. dp p f.
exists (p_pair (p_inl p0) p1)=>//=.

dp p f.
exists (p_pair (p_inr p0) p1)=>//=.

dp T f.
dp p f.
exists (p_fold (p_inl p_tt))=>//=.
dp p f.
exists (p_fold (p_inr (p_pair p0 p1))). ssa.

dp T f. 
exists p. ssa.

(*alredy apply interp even if it isn't needed, maybe improve this, fixed now*)

(*One-size induction*) 

move: T f. apply: pTree_1size_rect.
intros. dp2 u X f. dp2 p X f. 
 - dp2 p X f.
exists ((p_inl p_tt))=>//=.
-
dp2 p X f.
have: (forall x y : regex_regex__canonical__eqtype_Equality Af,
    (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).  
intros. apply f. done. 
move: H0. rewrite /pRel0 /=. lia.
move=>Hf.
move: (interp _ _ _ d p0 Hf).
case. move=> x [] Hsize Hflat. 
move: x Hsize Hflat. 
apply:pTree_case =>//;intros;inv_eq; inv pf;clear H0.
 * 
move: p Hsize Hflat. apply:pTree_case =>//;intros;inv_eq. clear H0.
rewrite -!eq_regex in Hsize Hflat. ssa.
(*We didn't find anything, so recurse*)
have: (pRel1 p1 (p_fold (p_inr (p_pair p0 p1)))).
rewrite /pRel1. simpl.  
move: (pTree_1size1 p0). lia. move=>HR.

have: (forall x y : regex,
    (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p1 -> post y T0).
intros. apply f. done.
move : H0. rewrite /pRel0.  ssa. lia. move=>Hf2.
move: (X p1 HR Hf2).
case. move=> x [] Hsize0 Hflat0.
move: x Hsize0 Hflat0. apply:pTree_case =>//;intros;inv_eq. clear H0.
inv pf1.
rewrite -!eq_regex in Hsize0 Hflat0. ssa.
move: p Hsize0 Hflat0. apply:pTree_case =>//;intros;inv_eq. 
clear H0.
rewrite -!eq_regex /= in Hsize0 Hflat0. subst.
exists (p_inl p_tt). ssa.   rewrite Hflat !Hflat0 //.
inv pf1. clear H0.
rewrite -!eq_regex in Hsize0 Hflat0. ssa. 
exists (p_inr p). ssa. lia. rewrite Hflat //.
* rewrite -!eq_regex in Hsize Hflat. ssa.   
  exists (p_inr (p_pair p  p1)).
ssa. lia.  rewrite Hflat //.  






(*peekinv case we don't need anymore*)
(*move: T f. apply: pTree_1size_rect.
intros. dp2 u X f. dp2 p X f. 
exists (p_fold (p_inl p_tt))=>//=.

dp2 p X f.
have: (forall x y : regex_regex__canonical__eqtype_Equality A,
    (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).  
intros. apply f. done. 
move: H0. rewrite /pRel0 /=. lia.
move=>Hf.
move: (interp _ _ _ d (p_inr p0) Hf).
case. move=> x [] Hsize Hflat. ssa.
exists (p_fold (p_inr (p_pair x p1))). ssa. lia. rewrite Hflat. done.
*)



(*move: x Hsize Hflat. 
apply:pTree_case =>//;intros;inv_eq; inv pf;clear H0.
 * 
move: p Hsize Hflat. apply:pTree_case =>//;intros;inv_eq. clear H0.
rewrite -!eq_regex in Hsize Hflat. ssa.
(*We didn't find anything, so recurse*)
have: (pRel1 p1 (p_fold (p_inr (p_pair p0 p1)))).
rewrite /pRel1. simpl.  
move: (pTree_1size1 p0). lia. move=>HR.

have: (forall x y : regex,
    (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p1 -> post y T0).
intros. apply f. done.
move : H0. rewrite /pRel0.  ssa. lia. move=>Hf2.
move: (X p1 HR Hf2).
case. move=> x [] Hsize0 Hflat0.
move: x Hsize0 Hflat0. apply:pTree_case =>//;intros;inv_eq. clear H0.
inv pf1.
rewrite -!eq_regex in Hsize0 Hflat0. ssa.
move: p Hsize0 Hflat0. apply:pTree_case =>//;intros;inv_eq. 
clear H0.
rewrite -!eq_regex /= in Hsize0 Hflat0. subst.
exists (p_inl p_tt). ssa.   rewrite Hflat !Hflat0 //.
inv pf1. clear H0.
rewrite -!eq_regex in Hsize0 Hflat0. ssa. 
exists (p_inr p). ssa. lia. rewrite Hflat //.
* rewrite -!eq_regex in Hsize Hflat. ssa.   
  exists (p_inr (p_pair p  p1)).
ssa. lia.  rewrite Hflat //.  


(*inv pf. clear H0.
rewrite -!eq_regex in Hsize Hflat. ssa. 

rewrite H1.


dp Hsize0 p2.
move: HR. 
inv pf. rewrite -eq_regex in H0.
exists (p_inl p_tt). ssa. rewrite H0.
rewrite -eq_regex in Hflat. subst. ssa.
Check eq_regex.
rewrite <- eq_regex. 

in H0.
Locate inv_eq.

Print inv_eq. Print can2_eq. Check can2_eq.
rewrite pf in H0.
 move : T f f' ; apply : pTree_case  => //; intros; inv_eq; move : f f' ;
   rewrite <- eq_regex; clear_eq => f f'
move: Hsize Hflat.
dp2 x X f. dp p X.
move: (X p1)=>/=. rewrite /pRel1 /=.
have: pTree_1size p1 < 1 + pTree_1size p1. lia. 
move=>Hsize. move/(_ Hsize). case=>x Hx.
exists x. ssa. 
move: (X p1)=>/=. rewrite /pRel1 /=.
have: pTree_1size p1 < pTree_1size p + pTree_1size p1. move: (pTree_1size1 p). lia.
move=>Hsize. move/(_ Hsize). case=>x Hx.
exists (p_fold (p_inr (p_pair p x))). ssa. lia. rewrite H0//.*)

(*admit.*)
(*One-size induction*)
(*clear f interp.
move: T. apply: pTree_1size_rect.
intros. dp u X. dp p X. dp p X.
exists (p_fold (p_inl p_tt))=>//=.
dp p X. 
move: (X p1)=>/=. rewrite /pRel1 /=.
have: pTree_1size p1 < pTree_1size p0 + pTree_1size p1.  move:(pTree_1size1 p0). lia.
move=>Hsize. move/(_ Hsize). case=>x Hx.
exists (p_fold (p_inr (p_pair (p_inr p0) x))). ssa. lia. rewrite H0//.*)
admit.*)

exists T. ssa.

case: (interp _ _ _ d T f)=> T' HT'. 
have:  (forall x y ,
         (x, y) \in l -> forall T0 : pTree x, pRel0 T0 T' -> post y T0).
intros. eapply f. eauto. move: H0. rewrite /pRel0. ssa. lia. move=>Hf. 
case: (interp _ _ _ d0 T' Hf)=>T2 HT2.  
exists T2. ssa. lia. rewrite H2 H0 //.

move: (interp _ _ _ d)=>H0.  
move: (interp _ _ _ d0)=>H1.  

dp T f. 
have: (forall x y, (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p -> post y T0).
intros. eapply f. eauto. done. 
move=>Hf0. 
case: (H0 p Hf0)=>T0 HT0.  
exists (p_inl T0)=>//. 

have: (forall x y, (x,y) \in l -> forall T0 : pTree x, pRel0 T0 p -> post y T0).
intros. eapply f. eauto. done. move=>Hf.
case: (H1 p Hf)=>T1 HT1. 
exists (p_inr T1)=>//. 

move: (interp _ _ _ d)=>H0.
move: (interp _ _ _ d0)=>H1. 
dp T f.
have: (forall x y,  (x,y) \in l  -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).
intros. eapply f. eauto. move: H2. rewrite /pRel0 //=. lia. move=>Hf0.
have: (forall x y, (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p1 -> post y T0).
intros. eapply f. eauto. move: H2. rewrite /pRel0 //=. lia. move=>Hf1.

case: (H0 p0 Hf0) =>T0' HT0'.
case: (H1 p1 Hf1) =>T1' HT1'.
exists (p_pair T0' T1')=>//=. ssa. lia. rewrite H4 H2 //. 



(*move: (interp _ _ _ d) f. 
(*One-size induction*)
clear interp d. 
move: T. apply: pTree_1size_rect.
intros. dp2 u f X. dp2 p f X. dp2 p f X.
exists (p_fold (p_inl p_tt))=>//=.
dp2 p f X. 
have: (forall x y, (x, y) \in l -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).
intros. eapply f. eauto. move: H0. rewrite /pRel0 //=. lia. 
move=>Hf.
case: (interp p0 Hf)=> x Hx. 
have: pRel1 p1 (p_fold (p_inr (p_pair p0 p1))). rewrite /pRel1 //=. move: (pTree_1size1 p0). lia.
move=>Hsize.
have: (forall x0 y,
    (x0, y) \in l -> forall T0 : pTree x0, pRel0 T0 p1 -> post y T0).
intros. eapply f. eauto. move: H0. rewrite /pRel0 /=.  lia.
move=>Hf'.
case: (X p1 Hsize interp Hf')=>x' Hx'. 
exists (p_fold (p_inr (p_pair x x'))). ssa. lia. rewrite H0 H2//.*)

dp T f. dp p0 f. 
have : pRel0 p1 (p_pair (p_singl s) p1). rewrite /pRel0 /=. lia.
move=>Hrel.
move: (f s0 s1 i p1 Hrel).
case. move=> x Hflat. ssa. 
exists (p_pair (p_singl s) x). 
ssa. f_equal. done. 

move : T f.
eapply (@pTree_0size_rect _ r0 (fun (T : pTree r0) => (forall x y,(x,y) \in l -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) -> post r1 T)).
move=> Hin IH Hf.
eapply (@interp _ _ _ p0 Hin). 
intros.
rewrite !inE in H.
destruct ((x,y) == (r0, r1)) eqn:Heqn.
case/eqP : Heqn. intros. subst.
eapply IH.  done.
move=> x' y' Hl T1 Hrel. eapply Hf. apply Hl. 
move: H0 Hrel. rewrite /pRel0. lia. 
simpl in H. 
eapply Hf. apply H. apply H0.
Defined.



Lemma dsl_sound : forall c0 c1, dsl nil c0 c1 -> (forall s, Match s c0 -> Match s c1).
Proof.
move=> c0 c1 d s Hmatch. 
case: (exists_pTree Hmatch) => x /eqP Hf. subst.
have: (forall  (x0 y : regex),
    (x0, y) \in nil -> forall T0 : pTree x0, pRel0 T0 x -> post y T0).
intros. done. move=>Hp.
move: (interp d x Hp). 
case. intros. ssa. rewrite H0. 
rewrite -uflatten_to_upTree.
apply pTree_Match. apply:to_typing.
Qed.


Section Decomposition.
Ltac pp := intros;apply:proj2_sig.

Lemma o_plus_l : forall c0 c1 R, (o (c0 _+_ c1)) <⟨R⟩= (o c0 _+_ o c1).
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto. 
Qed.

Lemma o_plus_r : forall c0 c1 R, (o c0 _+_ o c1)  <⟨R⟩=  (o (c0 _+_ c1)).
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto. 
Qed.

(*Lemma o_seq_l : forall c0 c1 R,  o (c0 _;_ c1) <⟨R⟩= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.*)

Lemma o_seq_r : forall c0 c1 R, o c0 _;_ o c1 <⟨R⟩=  o (c0 _;_ c1) .
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.

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

(*Lemma cstar1
     : forall c0 c1 P,
      c0 < ⟨P⟩= c1 ->  Star c0 < ⟨P⟩= Star c1. 
Proof. intros. apply:cstar;eauto.
Qed.*)


Ltac lct1 := apply:ctrans1.
Ltac lct2 := apply:ctrans2.
Ltac lcid := bt cid.
Ltac lcp1 := apply:cplus1.
Ltac lcp2 := apply:cplus2.
Ltac lcs1 := apply:cseq1.
Ltac lcs2 := apply:cseq2.
(*Ltac lcst1 := apply:cstar1.*)

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

Lemma factor_seq_l_l : forall R (B: eqType) l (P: B -> regex) c,   
\big[Plus/Empt]_(a <- l) (c _;_ P a) <⟨R⟩=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)) .
Proof.
move=> R B +P c. elim=>//=. econ. rewrite !big_nil //. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons //=.
lct2. apply:distLinv. lcp1. lcid. eauto. 
Qed.

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


Lemma factor_seq_r_l : forall R (B: eqType) l (P: B -> regex) c,  
\big[Plus/Empt]_(a <- l) (P a _;_ c) <⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c .
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct2. apply:distRinv. eauto. 
Qed.

Lemma factor_seq_r_r : forall R (B: eqType) l (P: B -> regex) c,  
(\big[Plus/Empt]_(a <- l) (P a)) _;_ c 
<⟨R⟩= 
\big[Plus/Empt]_(a <- l) (P a _;_ c) . 
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:distR. eauto. 
Qed.

(*Lemma eps_c_r : forall r R,   r < ⟨R⟩= r _;_ Eps.
Proof.
intros. econ. lct2. apply:swapinv. eauto. done. done.
Qed.

Hint Resolve eps_c_r.*)

Lemma eps_c_l : forall r R,   r _;_ Eps < ⟨R⟩= r .
Proof.
intros. econ. lct1. apply:swap. eauto. eauto.
Qed.

Hint Resolve eps_c_l.

Definition ex_coerce (l: seq Af) (F0 F1 : Af -> @regex Af) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus_c : forall (l : seq Af) F1 F2 R, ex_coerce l F1 F2 (dsl R) ->
   \big[Plus/Empt]_(i <- l) (F1 i) <⟨R⟩= \big[Plus/Empt]_(i <- l) (F2 i). 
Proof.
move=> + F1 F2 R. 
rewrite /ex_coerce. elim=>//.
move=> _. rewrite !big_nil//. 
move=> a l IH Hin. rewrite !big_cons /=. lcp1. apply:Hin. done.
eauto. 
Qed.

(*Lemma derive_seq_l : forall R a r r', a \ (r _;_ r') <⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') .
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /=. 
lcp1. lcid. eauto. 
intro.
rewrite /o Hcase /=.  eauto.
Qed.*)

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

Lemma com_seq_o_l : forall R r r', o(r) _;_ r' <⟨R⟩= r' _;_ o(r) .
Proof.
intros. rewrite /o. case Heq:(nu _)=>//=. eauto.  
Qed.

Lemma com_seq_o_r : forall R r r', r' _;_ o(r)  <⟨R⟩=  o(r) _;_ r' .
Proof.
intros. rewrite /o. case Heq:(nu _)=>//=. eauto.  
Qed.

Lemma plus_empt_l : forall (A: eqType) R (l : seq A),  \big[Plus/Empt]_(a <- l) (Empt) <⟨R⟩ = Empt .
Proof.
move=> B R. elim=>//=. rewrite big_nil //. 
move=> a l IH. rewrite big_cons. lct2. apply:untag. lcp1. lcid. eauto.
Qed.


Lemma big_event_notin_l R : forall l a, a \notin l ->   \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Empt . 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //. 
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite (negbTE Hneq).  move: (IH _ Hin). intros.
lct2. apply:untag. lcp1. eauto. eauto. 
Qed.

Lemma big_event_notin_r R : forall l a, a \notin l -> Empt  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a))  . 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //. eauto.
Qed.

Lemma empt_r_c : forall c R,  c _+_ Empt < ⟨R⟩= c .
Proof. eauto.
Qed.


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

(*Uses drop!*) (*ineffecient rule*)
(*Lemma star_o_l : forall R c c', Star (o (c) _+_ c') <⟨R⟩ = Star c' .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. 
eauto.
Qed.*)

(*Lemma star_o_r : forall R c c', Star c' <⟨R⟩ =  Star (o (c) _+_ c') .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.*)

Lemma derive_unfold_coerce : forall c, dsl nil c (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)).
Proof. 
elim;try solve [auto].
(*- con. eauto. rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 
- con. eauto. rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 
*)
- move=> s. 
 *  rewrite /o /=. lct2. apply:retag. lct2. apply:tagL.  
    apply:big_event_in_r. rewrite mem_index_enum //. 
(* *  rewrite /o /=. lct1. apply:untagL. apply:big_event_in_l. rewrite mem_index_enum //. *)
- move=> r0 Hd0 r1 Hd1.
   lct1. lcp1. apply:Hd0. apply:Hd1. 
   lct1. apply:shuffle. lct2. lcp1. apply: o_plus_r. lcid. 
   lct2. apply:shuffleinv. lcp1. lcid. 
   lct1. lct1. apply:retag. apply:shuffle. 
   lcp1. lcid. simpl. 
   lct2. apply:eq_big_plus_c. intro. intros. apply:distLinv.
   lct2. lct2.  apply:split_plus_r.  apply:retag. 
   lcp1. lcid. lcid. 
- move=> r0 Hd0 r1 Hd1.
  rewrite {1}/o /=.
  destruct (nu r0) eqn:Heqn;ssa;rewrite /o Heqn in Hd0.
  have:  (if nu r1 then Eps else Empt) = o r1. done.
  move=>->.

(*  destruct (nu r1) eqn:Heqn2;ssa.  *)
(*  rewrite /o Heqn Heqn2 in Hd0 Hd1.*)


  lct2. lcp2. 
  apply: eq_big_plus_c. intro. intros.
  lct2.
  apply distLinv. lcp1. apply:assoc. lcid. lcid.
  lct2. lcp2. lct2. apply split_plus_r. lcp1. apply/factor_seq_r_r. lcid. lcid.
  lct1.  lcs1. apply Hd0. lcid. (*only apply the first yet*)
  lct1. apply :distR. 
  lct1. lcp1. lct1. apply:proj. (*Because nu r0 = true, we will recurse in both cases of r0 Eps _+_ ..., apply Hd1 *) apply Hd1. lcid.
  lct1. apply shuffle. lcp1. lcid.
  lct1. apply:retag. lcid.


  (*This case is the optimization, r0 is not nullary, so don't use Hd1*) clear Hd1.
  lct2. lcp2. 
  apply: eq_big_plus_c. intro. intros.
  apply:assoc. lcid. 
  lct2. lcp2. apply/factor_seq_r_r. lcid. 
  lct1.  lcs1. apply Hd0. lcid. 
  lct1. apply :distR. 
  lct1. lcp1. apply:abortL. lcid. lcid.

(*See how similar the two cases are, drop = wrapinv for problematic terms*)
- move=> r0 Hd. rewrite /o /=.  
  lct2. lcp2. lct2. apply:eq_big_plus_c. intro. intros. apply:assoc.  apply:factor_seq_r_r.  lcid.
  move: Hd. rewrite /o. case_if;intros.
  lct1. apply:drop. apply Hd. lcid.
  lct1. apply:wrapinv.
  lcp1. lcid. lct1. 
  lcs1. apply Hd. lcid.
  lct1. apply distR. lct1. lcp1. apply:abortL.
  lcid. apply:untagL.
Qed.





Lemma derive_unfold_coerce2 : forall c, dsl nil (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)) c.
Proof.
elim;try solve [auto].
 rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 
  lct1. lcp2.  apply:eq_big_plus_c. intro. intros. apply:abortR. lcid.
  rewrite /o /=.
lct1. apply:untagL. apply:plus_empt_l.
- move=> s. 
(* *  rewrite /o /=. lct2. apply:retag. lct2. apply:tagL. 
    apply:big_event_in_r. rewrite mem_index_enum //. *)
 *  rewrite /o /=. lct1. apply:untagL. apply:big_event_in_l. rewrite mem_index_enum //. 
- move=> r0 Hd0 r1 Hd1.
   lct2. lcp1. apply:Hd0. apply:Hd1. 
   lct2. apply:shuffleinv. lct1. lcp1. apply: o_plus_l. lcid. 
   lct1. apply:shuffle. lcp1. lcid. 
   lct2. lct2. apply:retag. apply:shuffleinv. 
   lcp1. lcid. simpl. 
   lct1. apply:eq_big_plus_c. intro. intros. apply:distL.
   lct1. lct1.  apply:split_plus_l.  apply:retag. 
   lcp1. lcid. lcid. 
- move=> r0 Hd0 r1 Hd1.
  rewrite {1}/o /=.
  destruct (nu r0) eqn:Heqn;ssa;rewrite /o Heqn in Hd0.
  have:  (if nu r1 then Eps else Empt) = o r1. done.
  move=>->.

(*  destruct (nu r1) eqn:Heqn2;ssa.  *)
(*  rewrite /o Heqn Heqn2 in Hd0 Hd1.*)


  lct1. lcp2. 
  apply: eq_big_plus_c. intro. intros.
  lct1.
  apply distL. lcp1. apply:associnv. lcid. lcid.
  lct1. lcp2. lct1. apply split_plus_l. lcp1. apply/factor_seq_r_l. lcid. lcid.
  lct2.  lcs1. apply Hd0. lcid. (*only apply the first yet*)
  lct2. apply :distRinv. 
  lct2. lcp1. lct2. apply:projinv. (*Because nu r0 = true, we will recurse in both cases of r0 Eps _+_ ..., apply Hd1 *) apply Hd1. lcid.
  lct2. apply shuffleinv. lcp1. lcid.
  lct1. apply:retag. lcid.


  (*This case is the optimization, r0 is not nullary, so don't use Hd1*) clear Hd1.
  lct1. lcp2. 
  apply: eq_big_plus_c. intro. intros.
  apply:associnv. lcid. 
  lct1. lcp2. apply/factor_seq_r_l. lcid. 
  lct2.  lcs1. apply Hd0. lcid. 
  lct2. apply :distRinv. 
  lct2. lcp1. apply:abortLinv. lcid. lcid.

(*See how similar the two cases are, drop = wrapinv for problematic terms*)
- move=> r0 Hd. rewrite /o /=.  
  lct1. lcp2. lct1. apply:eq_big_plus_c. intro. intros. apply:associnv.  apply:factor_seq_r_l. lcid.
  move: Hd. rewrite /o. case_if;intros.
  lct2. apply:dropinv. apply Hd. lcid.
  lct2. apply:wrap.
  lcp1. lcid. lct2. 
  lcs1. apply Hd. lcid.
  lct2. apply distRinv. lct2. lcp1. apply:abortLinv.
  lcid. apply:untagLinv.
Qed.



(*Lemma derive_unfold_coerce : forall c, dsl nil c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c))  *
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
Qed.*)



Lemma derive_unfold_coerce_l : forall c,  dsl nil c (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)). 
Proof.
(*intros. destruct (derive_unfold_coerce c). done.*)
intros. apply derive_unfold_coerce.
Qed.

Lemma derive_unfold_coerce_r : forall c, dsl nil (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)) c.
Proof.
intros. apply derive_unfold_coerce2.
Qed.



Lemma nu_imp_coerce_aux : forall r0 r1, (nu r0 -> nu r1) ->  o r0 <⟨nil⟩= o r1. 
Proof.
intros. destruct (nu r0) eqn:Heqn. rewrite /o Heqn H //. econ. lcid. 
rewrite /o Heqn.
destruct (nu r1). econ.
lct2. apply:untagL.
apply:tagL.
eauto. done.
Qed.

Lemma big_plus_coerce : forall (l : seq Af) F0 F1 R, (forall a, a \in l ->  (F0 a,F1 a) \in R) ->
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

Lemma nu_false : nu (\big[Plus/Empt]_(a : Af) (Event a _;_ Empt)) = false.
Proof.
move: (index_enum Af)=> l.
elim: l;ssa.
rewrite !big_nil. ssa.
rewrite !big_cons. ssa.
Qed.

Lemma nu_has : forall (l : @pder Af), nu (\big[Plus/Empt]_(i <- l) i) = has nu l.
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
have: a \in index_enum Af by done. 
move : (index_enum Af)=>l.
elim: l;ssa. rewrite !big_cons. rewrite !inE in H. simpl.
destruct (eqVneq a a0). subst. 
lct2. lcp1. apply:projinv.  lcid. eauto.
lct1. apply X. ssa. eauto.
Qed.

Lemma big_event_notin_lF R : forall (l : seq Af) a (F : Af -> regex), a \notin l ->   a \ \big[Plus/Empt]_(i <- l) (Event i _;_ (F i)) <⟨R⟩= Empt . 
Proof.
elim=>//=;ssa. rewrite !big_nil //.
rewrite  !inE in H.  ssa.
rewrite !big_cons. ssa.  rewrite eq_sym (negbTE H0). 
lct1. lcp1. instantiate (1:= Empt). eauto. apply:X. done. eauto.
Qed.

Lemma big_plus2 : forall a F, a \ \big[Plus/Empt]_a0 (Event a0 _;_ F a0) <⟨nil⟩=  F a.
Proof.
move=> a.
have: a \in index_enum Af by done. 
move : (index_enum Af)=>l.
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


Lemma o_o_l : forall l, o (\big[Plus/Empt]_(i <- l) i) < ⟨ [::] ⟩ = o_l l.
Proof.
intros. rewrite /o /o_l nu_has //. 
Qed.

Lemma o_o_l2 : forall l, o_l l < ⟨ [::] ⟩ =   o (\big[Plus/Empt]_(i <- l) i). 
Proof.
intros. rewrite /o /o_l nu_has //. 
Qed.



Lemma decomp_p1_aux : forall l ,  \big[Plus/Empt]_(i <- l) i <⟨nil⟩= (o_l l) _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof. 
intros. 
lct1. apply:derive_unfold_coerce_l.
apply:cplus. apply:o_o_l.
apply:eq_big_plus_c.
intro. intros. apply:cseq. lcid. rewrite -pd_plus.
lct2. apply:c_eq_undup2. apply:c_eq_derive_pd_l1.
Qed.

(*Lemma decomp_p1_aux : forall l ,  \big[Plus/Empt]_(i <- l) i <⟨nil⟩= (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
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
Qed.*)

Lemma dsl_mon : forall l l' E F, dsl l E F -> is_sub_bool l l' ->  dsl l' E F.
Proof.
move=> l l' E F p. 
elim: p l';auto with dsl;simpl;intros.
apply:ctrans. eauto. eauto.
apply:dsl_var. move/is_subP : H=>Hsub. apply Hsub. done.
apply:dsl_fix. apply:X. ssa.
apply/is_subP. move/is_subP : H.
intro. intro. move/H. rewrite !inE. move=>->//. lia.
Qed.

Lemma decomp_p1 : forall l L ,  \big[Plus/Empt]_(i <- l) i <⟨L⟩= (o_l l) _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof.
intros. apply/dsl_mon. apply/decomp_p1_aux. eauto.
Qed.

Lemma nu_plus : forall (A' : Type)l (F : A' -> @regex Af), nu(\big[Plus/Empt]_(a <- l) (F a)) = has (fun x => nu (F x)) l.
Proof.
move=> A'.
elim;ssa. rewrite !big_nil. ssa.
rewrite !big_cons. simpl. f_equal. done.
Qed.

Lemma has_xpred0 : forall (A : Type) (l : seq A), has xpred0 l = false.
Proof.
move=> A. elim;ssa.
Qed.

Lemma decomp_p2_aux : forall l,  (o_l l) _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨nil⟩=  \big[Plus/Empt]_(i <- l) i.
Proof. 
intros. 
lct2. apply:derive_unfold_coerce_r.
apply:cplus. 
apply:o_o_l2.
apply:eq_big_plus_c.
intro. intros. apply:cseq. lcid. rewrite -pd_plus.
lct1. apply:c_eq_undup1. apply:c_eq_derive_pd_l2.
Qed.

(*Lemma decomp_p2_aux : forall l,  (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨nil⟩=  \big[Plus/Empt]_(i <- l) i.
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
Qed.*)

Lemma decomp_p2 : forall l L,  (o_l l) _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨L⟩=  \big[Plus/Empt]_(i <- l) i.
Proof.
intros. apply/dsl_mon. apply/decomp_p2_aux. eauto.
Qed.

End Decomposition.

Section Decidability.
Definition check_o := (fun ( l0 l1 : @pder Af) => has nu l0 ==> has nu l1).

Inductive exten_gen bisim : pder -> pder-> Prop :=
 contains_con2 l0 l1 (H0: forall e, bisim (pd_l e l0) (pd_l e l1) : Prop ) (H1: check_o l0 l1 (*has nu l0 = has nu l1*)) : exten_gen bisim l0 l1.

Definition Extensional l0 l1 := paco2 exten_gen bot2 l0 l1.
Hint Unfold  Extensional : core.

Lemma exten_gen_mon: monotone2 exten_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve exten_gen_mon : paco.

Definition contains_l s (l0 l1 : @pder Af) := Match s (\big[Plus/Empt]_(a <- l0) a) -> Match s (\big[Plus/Empt]_(a <- l1) a).

Lemma Pb_P_iff : forall l l', check_o l l' <->
                           contains_l [::] l l'.
Proof.
intros. rewrite /check_o /contains_l.
rewrite -!Match_has_nu_iff. split. move/implyP=>//.  
move/implyP=>//.
Qed.

Lemma P_derive : forall a l0 l1, forall s, contains_l s  (pd_l a l0) (pd_l a l1) <-> contains_l (a :: s) l0 l1.  
Proof.
intros. rewrite /contains_l.
rewrite -!pd_plus. rewrite !Match_big_undup.
rewrite !deriveP2. done.
Qed.


Lemma P_undup : forall l0 l1, (forall s, contains_l s l0 l1  <-> contains_l s (undup l0) (undup l1)).
Proof.
intros. rewrite /contains_l. rewrite !Match_big_undup //.
Qed.


Theorem equiv_rInd : forall l l', Extensional l l' -> forall s, contains_l s l l'.  
Proof.
move=> l0 l1 HC s. 
elim: s l0 l1  HC.
- move=> c0 c1. intros. punfold HC. case: HC. move=> ce c3 HC HC'.
  apply Pb_P_iff. done.
- move=> a l IH c0 c1. move=>HC.  punfold HC. case: HC. intros.
  case: (H0 a)=>//. intros.
  apply/P_derive. apply IH. done.
Qed.

Theorem Bisim_co_ind : forall l l', (forall s, contains_l s l l') -> Extensional l l'.
Proof.
pcofix CIH. move=> l l'. pfold. con. 
intros. right. apply:CIH. intros.
apply P_derive. apply H0.
apply/Pb_P_iff. done.
Qed.

Lemma Extensional_equiv : forall l l', Extensional l l' <->  forall s, contains_l s l l'. 
Proof.
intros. split. apply/equiv_rInd. apply:Bisim_co_ind.
Qed.


Fixpoint bisim_complete_aux p l_v (H : D_bisim l_v p) {struct H} :  Extensional p.1 p.2 ->  reachable check_o H.  
refine( match H with 
        | Db_stop x y z => _ 
        | _ => _ 
        end).
simpl in x,y,z. intros.
have:  exten_gen (upaco2 exten_gen bot2) y.1 y.2. clear bisim_complete_aux. punfold H0.
clear H0. move=> He.  move: He z. case.
intros. simpl. destruct (Utils.dec _). done.
exfalso. rewrite z in e. done.
simpl in p0. intros.
have:  exten_gen (upaco2 exten_gen bot2) p1.1 p1.2.
punfold H0.
clear H0=>H0. destruct p1. simpl in *.
destruct (Utils.dec _). done.
move: H0 i i0 d. clear e.
case. intros. ssa. 
apply/allP. intro. intros.
apply (bisim_complete_aux _ _ (d x)). simpl.
clear bisim_complete_aux. simpl. case: (H0 x). ssa. done.
Qed.

Lemma bisim_complete : forall l0 l1, Extensional l0 l1 ->  reachable_wrap l0 l1 check_o.
Proof. intros. apply:bisim_complete_aux. apply/Extensional_equiv. 
intro. apply -> P_undup. move: s. apply/Extensional_equiv=>//.
Qed.

Fixpoint bisim_sound_aux p l_v (H : D_bisim l_v p) (R : @pder Af -> @pder Af -> Prop) {struct H} : 
(forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   reachable check_o H -> upaco2 exten_gen R p.1 p.2. 
refine( match H with 
        | Db_stop x y z => _ 
        | _ => _ 
        end).
- ssa. right.  apply/H0. destruct y. ssa. 
- simpl. intros. left. destruct (Utils.dec _). rewrite e in i. done.
  destruct (andP H1). pcofix CIH. pfold. con. intros. 
  eapply (bisim_sound_aux (pd_l e0 p1.1,pd_l e0 p1.2)).  
  simpl. 2: { apply (allP H3). done. } 
  intros. rewrite !inE in H4. destruct (orP H4). 
  norm_eqs. ssa.  eauto. done.
Qed.

Lemma bisim_sound : forall e0 e1, reachable_wrap e0 e1 check_o -> Extensional e0 e1.  
Proof. move => e0 e1 H. rewrite /reachable_wrap in H. 
apply:Bisim_co_ind=>s. apply/P_undup. move: s. apply/Extensional_equiv.
apply (@bisim_sound_aux _ _ _ bot2) in H. ssa. inv H. ssa.
Qed.

Lemma P_decidable : forall l0 l1, reachable_wrap l0 l1 check_o <-> (forall s, contains_l s l0 l1).
Proof. intros. split. move/bisim_sound. move/Extensional_equiv.
move=> H s. eauto. intros. apply/bisim_complete. apply/Bisim_co_ind. done.
Qed.
End Decidability.

Section Completeness.
(*To avoid universe inconsistency we create a type similar to sumbool*)
Inductive sumboolT (A B : Type) : Type := 
 | leftT : A -> sumboolT A B
 | rightT : B -> sumboolT A B.



Lemma reachable_simp : forall V l (H : D_bisim V l) (Hnot: l\notin V), reachable check_o H = 
                                                              (check_o l.1 l.2) && (all (fun (a : Af) => reachable  check_o (D_bisim_proj H Hnot a)) (index_enum Af)).
Proof.
intros. destruct H.  ssa. exfalso.
rewrite i in Hnot. done. ssa. rewrite (negbTE Hnot) /=. ssa.
Qed.

Fixpoint proof_irrel  V l (H H' : D_bisim V l) {struct H} : reachable check_o H = reachable check_o H'.
Proof.
refine (
match H in D_bisim V' l' return V' = V -> l' = l -> reachable check_o H = reachable check_o H' with 
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

Fixpoint EQ_complete_aux p (V : seq (@pder Af * @pder Af)) (H : D_bisim V p) {struct H} : forall (L : seq (@regex Af * @regex Af)),
    (forall x y, (x,y) \in V ->  (\big[Plus/Empt]_(i <- x) i, \big[Plus/Empt]_(i <- y) i) \in L) -> 
                                                         reachable check_o H -> 
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
move:(index_enum Af)=> lA.
elim: lA. 
ssa. rewrite !big_nil. done.
ssa. rewrite !big_cons. apply:cplus. done.
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



Lemma bisim_c_eq : forall l l', reachable_wrap l l' check_o ->  (\big[Plus/Empt]_(i <- l) i) <⟨nil⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. apply (@EQ_complete_aux _ _ _ nil) in H. destruct H. done. simpl in d.
apply:ctrans. apply c_eq_undup2.  apply:ctrans.
2: apply c_eq_undup1. done. 
ssa.
Qed.

Lemma equiv_r_plus : forall (c0 c1 : @regex Af), contains_r c0 c1 -> contains_r (\big[Plus/Empt]_(i <- c0::nil) i)  (\big[Plus/Empt]_(i <- c1::nil) i).
Proof.
intros. intro. ssa. move: H0. rewrite !big_cons !big_nil. intros. inv H0;eauto. con. apply/H. done.
inv H3.
Qed.


Lemma c_eq_completeness : forall (c0 c1 : regex), contains_r c0 c1 -> c0 <⟨nil⟩= c1.
Proof. move=> c0 c1. move/equiv_r_plus. move/Bisim_co_ind. move/bisim_complete.
move/bisim_c_eq. rewrite !big_cons !big_nil. eauto.
Qed.
End Completeness.
End DSL.





(*Extraction*)
(*Require Import Containment.constructiveEps.*)
Lemma contains_seq1 : forall (Af : finType) (r0 r1 : @regex Af), contains_r r0 r1 <-> contains_r (\big[Plus/Empt]_(a <- r0::nil) a) (\big[Plus/Empt]_(a <- r1::nil) a).
Proof.
intros. split.
intros. rewrite !big_cons !big_nil. 
intro. ssa. inv H0. con. eauto. inv H3.
rewrite !big_cons !big_nil.
intros. intro. 
intros. suff: Match s (r1 _+_ Empt).
intros. inv H1. inv H4.
apply:H. con. done.
Qed.


Lemma synth_coercion : forall {Af : finType} (r0 r1 : @regex Af), option (dsl nil r0 r1). 
Proof.
intros. 
destruct (enum.reachable_wrap [::r0] [::r1] check_o) eqn:Heqn.
move/P_decidable : Heqn. move=>HH. con. apply:c_eq_completeness.  apply/contains_seq1. done.
apply : None.
Qed.


Definition myFin := ordinal 2.
Definition synth_coercion_wrap := @synth_coercion myFin.
(*Definition upT : upTree myFin := (up_fold (up_inr (up_pair (up_singl ord0) (up_fold (up_inl up_tt))))).
Definition re_star : @regex myFin := Star (Event ord0).

Definition tp : typingb upT re_star := is_true_true.  

Print eqP.*)

(*Definition gen_trees  (n : nat) (r : @regex myFin) : seq (pTree r). 
move : ((gen_upTree myFin n)) => l.
elim : l. apply : nil.
intros. destruct (typingb a r) eqn:Heqn. apply typingP1 in Heqn.
apply to_pTree in Heqn. apply : cons. apply Heqn. apply X.
apply : X.
Defined.*)



(*Definition test : @pTree myFin (derive ord0 (Seq (Event ord0) Eps)).
simpl. con. con. con.
Defined.
*)
(*Eval vm_compute in (derive_pTreeP ord0 _ test).*)


Fixpoint inc_seq (n : nat) (l : seq nat) := 
match l with 
| nil => nil 
| a::l' => if a.+1 < n then a.+1::l' 
         else 0::(inc_seq n l')
end.
Definition to_string (A : Type) (a : A) (aa : seq A) (l : seq nat) := map (nth a aa) l.
Fixpoint seq_first (A B : Type) (P : A -> option B) (l : seq A) := 
match l with 
| nil => None 
| a::l' => if P a is Some a then Some a else seq_first P l'
end. 
Fixpoint quick_parse_aux  (n : nat) (l : seq myFin) (r: @regex myFin) : option ((seq myFin) * (pTree r)).
refine(
if n is n'.+1 then
match r with 
 | Eps => if l == nil then (Some (nil,p_tt)) else None
 | Empt => None 
 | Event s => if l is (x::l') then if x == s then  Some (l',p_singl _) else None  else None
 | Plus r0 r1 => if quick_parse_aux n' l r0 is Some (l',T) then Some (l',p_inl T) 
                else if quick_parse_aux n' l  r1 is Some (l',T) then Some (l',p_inr T) else None 
 | Seq r0 r1 => if quick_parse_aux n' l r0 is Some (l',T) then 
                 if quick_parse_aux n' l' r1 is Some (l'',T') then Some (l'',p_pair T T') else None else None 
 | Star r0 => _ (* quick_parse_aux n' l (Eps _+_ r0 _;_ (Star r0)) with *)
end
else None).
destruct (quick_parse_aux n' l (Eps _+_ r0 _;_ (Star r0))). destruct p.

move : p. apply:pTree_case;try solve [intros;exfalso;ssa].
intros. inversion pf. subst. apply (Some (l0,p_fold (p_inl p))).
intros. inversion pf. subst.
move : p. apply:pTree_case;try solve [intros;exfalso;ssa].
intros. inversion pf0. subst. apply (Some (l0,p_fold (p_inr (p_pair p0 p1)))).
apply None.
Defined.

(*Definition big_nat : nat := 1000000000.*)

Definition quick_parse (n : nat) (l : seq myFin) (r: @regex myFin) : option ((pTree r)) := 
if quick_parse_aux n l r is Some (l,T) then if l is nil then Some T else None else None.

Definition parse_inc  (n : nat) (r : @regex myFin) (l : seq nat) := 
match quick_parse n (to_string ord0 (index_enum myFin) l) r with 
| Some t => inr ( t)
| None => inl (inc_seq (size (index_enum myFin)) l)
end.


(*n = fuel for rep_try parse
  n2 = fuel for parse *)
Fixpoint rep_try_parse (n n2 : nat) (r: @regex myFin) (l : seq nat) := 
if n is n'.+1 then 
match parse_inc n2  r l with 
| inr t => Some t 
| inl l' => if l == l' then None else  rep_try_parse n' n2 r  l' 
end 
else None.

Definition my_parse (fuel size : nat) (r: @regex myFin) := rep_try_parse fuel fuel r (nseq size 0).
Definition interp_wrap {r0 r1 : @regex myFin} (d : dsl nil r0 r1) (T : pTree r0) : post r1 T.
apply:interp. apply:d. intros. exfalso. discriminate.
Defined.

Fixpoint dsl_size {l} {r0 r1 : @regex myFin} (d : dsl l r0 r1) : nat := 
match d with 
| ctrans _ _ _ d0 d1 => (dsl_size d0) + (dsl_size d1)
| cplus _ _ _ _ d0 d1 =>  (dsl_size d0) + (dsl_size d1)
| cseq _ _ _ _ d0 d1 =>  (dsl_size d0) + (dsl_size d1)
| dsl_fix _ _ d0 =>  (dsl_size d0)
| _ => 1
end.

Definition time_synth_coercion := @synth_coercion_wrap.
Definition time_interp_wrap := @interp_wrap.

Definition interp_size (r0 r1: @regex myFin) (prog : dsl nil r0 r1) := (fun T0 => (pTree_1size T0,proj1_sig (time_interp_wrap prog T0))).

Definition synth_interp (n : nat) (l : seq nat) (r0 r1 : @regex myFin): option (nat * seq (nat * pTree r1)) :=
match time_synth_coercion r0 r1 with 
| Some prog => let Ts := pmap (fun x => my_parse n x r0) l
              in if size Ts != size l then None 
              else Some ((dsl_size prog), map (@interp_size r0 r1 prog) Ts) (*(fun T0 => (pTree_1size T0,proj1_sig (time_interp_wrap prog T0))) Ts)*)
| None => None
end.

(*Definition only_synth  (n : Decimal.signed_int) (x : nat) (r0 r1 : @regex myFin): option (Decimal.signed_int *  (pTree r1)) :=
match time_synth_coercion r0 r1 with 
| Some prog => if my_parse n' x r0 is Some T0
              then Some (Nat.to_int (dsl_size prog), (proj1_sig (time_interp_wrap prog T0))) else None
| None => None
end
else None.*)

(*Definition synth_interp1 (n : Decimal.signed_int) (x : nat) (r0 r1 : @regex myFin): option (Decimal.signed_int *  (pTree r1)) :=
if Nat.of_int n is Some n' then
match time_synth_coercion r0 r1 with 
| Some prog => if my_parse n' x r0 is Some T0
              then Some (Nat.to_int (dsl_size prog), (proj1_sig (time_interp_wrap prog T0))) else None
| None => None
end
else None.

Definition no_synth_interp1 (n : Decimal.signed_int) (x : nat) (r0 r1 : @regex myFin) (prog : dsl nil r0 r1): option (Decimal.signed_int *  (pTree r1)) :=
if Nat.of_int n is Some n' then
if my_parse n' x r0 is Some T0
              then Some (Nat.to_int (dsl_size prog), (proj1_sig (time_interp_wrap prog T0))) else None
else None.*)

Require Import  extraction.ExtrOcamlString.
Require Import extraction.ExtrOcamlNatInt.
Require Import String.


Definition big_nat := 1000000. 
(*(Pos ( (( D1 (D1 (D1 (D1 (D1 (D1 (D1 Nil)))))))))).*)
Definition tree_sizes : seq nat := [:: 5000;500;50].

(*Definition only_synth := (fun _ : unit => time_synth_coercion (fst (snd rp1)) (snd (snd rp1))).
Definition no_synth_interp1_applied := (fun _ : unit => @no_synth_interp1 big_nat  50000  (fst (snd rp1)) (snd (snd rp1))).*)

Definition synth_interp_applied := synth_interp big_nat tree_sizes.

(*Definition synth_interp1_applied1 := (fun _ : unit => synth_interp1 big_nat 50000 (fst (snd rp1))(snd (snd rp1))).
Definition synth_interp1_applied2 := (fun _ : unit => synth_interp1 big_nat 5000 (fst (snd rp1))(snd (snd rp1))).
Definition synth_interp1_applied3 := (fun _ : unit => synth_interp1 big_nat 500 (fst (snd rp1))(snd (snd rp1))).
*)

Definition print_label (s : string) := id s. 

Definition re_pair := (string * ((@regex myFin) * (@regex myFin)))%type. 
Definition eval_test (rp : re_pair) := 
let _ := print_label (fst rp) in 
synth_interp_applied (fst (snd rp)) (snd (snd rp)).

(*a = 0*)
Definition a : @regex myFin:= Event ord0.

(*b = 1*)
Definition b : @regex myFin. apply Event. econ. instantiate (1:= 1). done. 
Defined.

Definition star_a := Star a.
Definition star_star_a := Star (star_a).

Definition rp1 := ("a^* x (a^*)^* <= a^*", (star_a _;_ star_star_a,star_a)).
Definition rp1' := ("a ^* <= a^* x (a^*)^*", (star_a, star_a _;_ star_star_a)).

Definition rp2 := ("(a^*)^* <= a^*",(star_star_a,star_a)).
Definition rp2' := (" a^* <= (a^*)^*",(star_a,star_star_a)). 

Definition rp3 := ("(1 + a)^* <= a^*",(Star (Eps _+_ a),star_a)).
Definition rp3' := ("a^* <= (1 + a)^*",(star_a,Star (Eps _+_ a))). 

Definition rp4 := ("(a+b)^* <= a^* + (b^* x a^*)^*",(Star (a _+_ b), (Star a) _+_ (Star ((Star b) _;_ (Star a))))). 
Definition rp4' := ("a^* + (b^* x a^*)^* <= (a + b)^*",((Star a) _+_ (Star (b _;_ (Star a))), Star (a _+_ b) )).

Definition rp5 := ("a^* x b^* <= ((1 + a) x (1 + b))^*",((Star a) _;_ (Star b),Star ((Eps _+_ a) _;_ (Eps _+_ b)))). 
(*Definition rp5' := ("((1 + a) x (1 + b))^* <= a^* x b^*  ",(Star ((Eps _+_ a) _;_ (Eps _+_ b)),((Star a) _;_ (Star b)))).*) (*Not true*)

Definition rp6 := ("a^* x (1 + a) <= a^*",((Star a) _;_ (Eps _+_ a),Star a)).
Definition rp6' := ("a^* <= a^* x (1 + a)",(Star a,(Star a) _;_ (Eps _+_ a))).

(*Takes too long to generate test data for these examples*)
(*
Definition rp7 := ("b _+_ a^* x b <= a^* x b",(b _+_ ((Star a) _;_ b),(Star a) _;_ b)). (*error*)
Definition rp7' := ("a^* x b <= b _+_ a^* x b",((Star a) _;_ b,(b _+_ ((Star a) _;_ b)))). (*error*)

Definition rp8 := ("b + b x a^* <= b x a^*",(b _+_ (b _;_ (Star a)), b _;_ (Star a))). (*error*)
Definition rp8' := (" b x a^* <= b + b x a^*",((b _;_ (Star a)),b _+_ (b _;_ (Star a)))).*)

Definition rp7 := ("(a + b)^* <= (a^* + b^*)^*",(Star (a _+_ b),Star ((Star a) _+_ (Star b)))).
Definition rp7' := ("(a^* + b^*)^* <= (a + b)^*",(Star ((Star a) _+_ (Star b)),Star (a _+_ b))).

Definition rp8 := ("(a^* + b^*)^* <= (a^* x b^*)^*",(Star ((Star a) _+_ (Star b)), Star ((Star a) _;_ (Star b)))).
Definition rp8' := ("(a^* x b^*)^* <= (a^* + b^*)^*",(Star ((Star a) _;_ (Star b)),Star ((Star a) _+_ (Star b)))).

Definition make_test (rp : re_pair) := fun (_ : unit) => eval_test rp.
Definition test1 := make_test rp1.
Definition test1' := make_test rp1'.

Definition test2 := make_test rp2.
Definition test2' := make_test rp2'.

Definition test3 := make_test rp3.
Definition test3' := make_test rp3'.

Definition test4 := make_test rp4.
Definition test4' := make_test rp4'.

Definition test5 := make_test rp5.
(*Definition test5' := make_test rp5'.*)

Definition test6 := make_test rp6.
Definition test6' := make_test rp6'.

(*Definition test7 := make_test rp7.
Definition test7' := make_test rp7'.

Definition test8 := make_test rp8.
Definition test8' := make_test rp8'.*)

Definition test7 := make_test rp7.

Definition test7' := make_test rp7'.

Definition test8 := make_test rp8.
Definition test8' := make_test rp8'.


(*Definition make_test2 (p :re_pair) := fun (_ : unit) => time_synth_coercion (fst (snd p)) (snd (snd p)).
Definition test_bad7 := make_test2 rp7.
Definition test_bad7' := make_test2 rp7'.
Definition test_bad8 := make_test2 rp8.
Definition test_bad := (test_bad7,test_bad7',test_bad8).*)
Definition test := (test1,test1',test2,test2',test3,test3',test4,test4',test5,test6,test6',test7,test7',test8,test8'). (*,test9,test9',test10,test10',test_bad).*)

(*Extraction "../bench/lib/mytest" test.*)


(*Extraction "../bench/lib/testsuite" test.*)



Require Import Containment.constructiveEps.

Lemma synth_coercion_slow : forall  (r0 r1 : @regex myFin), option (pTree r0 -> pTree r1). 
Proof.
intros. 
destruct (enum.reachable_wrap [::r0] [::r1] check_o) eqn:Heqn.
move/P_decidable : Heqn. move=>HH. con. apply:constr_eps_coerce.
apply/contains_seq1. done.
apply : None.
Qed.

Definition time_synth_coercion_slow := synth_coercion_slow.

Definition slow_synth_interp (n : nat) (l : seq nat) (r0 r1 : @regex myFin): option (seq (pTree r1)) :=
match time_synth_coercion_slow r0 r1 with 
| Some prog => let Ts := pmap (fun x => my_parse n x r0) l
              in if size Ts != size l then None 
              else Some (map (prog) Ts) (*(fun T0 => (pTree_1size T0,proj1_sig (time_interp_wrap prog T0))) Ts)*)
| None => None
end.

Definition slow_synth_interp_applied := slow_synth_interp big_nat [::50].

Definition slow_eval_test (rp : re_pair) := 
let _ := print_label (fst rp) in 
slow_synth_interp_applied (fst (snd rp)) (snd (snd rp)).
Definition slow_make_test (rp : re_pair) := fun (_ : unit) => slow_eval_test rp.

Definition slowtest := slow_make_test rp1.




(*Extraction "../bench/lib/slowtest" slowtest.*)


(*Definition rps := [::rp1;rp1';rp2;rp2';rp3;rp3';rp4;rp4';rp5;rp5';rp6;rp6';rp7;rp7';rp8;rp8';rp9;rp9;rp10;rp10'].*)



(*Definition suitetwo := (eval_test,rps). (*synth_interp1_applied1,synth_interp1_applied2,synth_interp1_applied3,@no_synth_interp1_applied,only_synth).*)
Extraction "../bench/lib/suitetwo" suitetwo. 
Extraction rps.

(*Fixpoint map_unit {A : Type} { B : Type ->  Type} (f :  A ->  B A) (l : seq A) :=
match l with 
| nil => tt 
| a::l' => let _ := f a in map_unit f l'
end.
Check eval_test.
Definition eval_tests (rps : seq re_pair) := 
@map_unit _ (fun A => option (nat * seq (pTree rp.2.2)))  eval_test  rps.*)



Definition re1 : @regex myFin := Seq (Star (Event ord0)) (Star (Star (Event ord0))).
Definition re2 : @regex myFin := Star (Event ord0).

Definition re_nat : @regex nat := Seq (Star (Event 0)) (Star (Star (Event 0))).

Definition test_string := to_string 0 ([:: 0 ;1 ;2]) (nseq (2000) 0).
*)



(*Definition my_parse_int (fuel size : Decimal.signed_int) (r: @regex myFin) := rep_try_parse (Nat.of_int fuel) r (nseq (Nat.of_int size) 0).*)




Definition my_synth := @synth_coercion myFin.


(*Definition my_test (r0 r1 : @regex myFin) (n : Decimal.signed_int) : option (pTree r0) :=
match my_synth r0 r1 with (* as x return match x with | Some prog => match (gen_tree n r0) with | Some p => post r1 p | None => unit end | None => unit end   with *)
| Some prog =>  my_parse 100000 (Nat.of_int n) r0 
| None => None
end.
*)
Require Import Decimal.



(*Eval vm_compute in (Nat.of_int (Pos ( (D1 ( D1 (  D1 (D1 (D0 Nil)))))))). (Pos (D1 Nil))).*)
Definition test1 := (re1,re2,Pos ( (( (D1 (D0 Nil)))))). 
(*111 110*)
(*Definition trees := gen_strings 100 re1.*)


Definition eval_test (t : test_case) := my_test (fst (fst t)) (snd (fst t)) (snd t).

(*Definition test_string := to_string ord0 (index_enum myFin) (nseq (150) 0).*)
(*Definition test_parse := fun (_ : unit) => parse test_string re1.*)
(*Definition my_parse_test := my_parse 1000 2 re1.*)
Definition suiteone := (test1,eval_test).
Extraction Inline Datatypes_nat__canonical__choice_Countable.
Extraction Inline solution_left.
Extraction Inline solution_right.
Extraction Inline simplification_heq.
Extraction Inline pTree_0size_rect.
Extraction Inline pTree_1size_rect.
Extraction Inline pTree_case.
(* Extraction Implicit my_test [r0 r1]. *)

Extraction "../bench/lib/suiteone" suiteone. 


(*Extraction Implicit p_pair [ A r0 r1].
Extraction Implicit p_inl [ A r0 r1].
Extraction Implicit p_inr [ A r0 r1].
Extraction Implicit p_fold [ A r ].

Check @interp.




Extraction Implicit shuffle [R A B C].

Extraction synth_coercion.

Extraction Implicit shuffleinv [R A B C].
Extraction Implicit retag [R A B].
Extraction Implicit untagL [R A].
Extraction Implicit untagLinv [R A].
Extraction Implicit untag [R A].
Extraction Implicit tagL [R A B].
Extraction Implicit assoc [R A B C].
Extraction Implicit associnv [R A B C].
Extraction Implicit swap [R A].
Extraction Implicit swapinv [R A].
Extraction Implicit proj [R A].
Extraction Implicit projinv [R A].
Extraction Implicit abortR [R A].
Extraction Implicit abortRinv [R A].
Extraction Implicit abortL [R A].
Extraction Implicit abortLinv [R A].
Extraction Implicit distL [R A B C].
Extraction Implicit distLinv [R A B C].
Extraction Implicit distR [R A B C].
Extraction Implicit distRinv [R A B C].
Extraction Implicit wrap [R A]. 
Extraction Implicit wrapinv [R A].
Extraction Implicit drop [R A B].
Extraction Implicit dropinv [R A B].
Extraction Implicit cid [R A].
Extraction Implicit ctrans [R A B C].
Extraction Implicit cplus [R A A' B B'].
Extraction Implicit cseq [R A  A' B B' ].
Extraction Implicit dsl_var [R].
Extraction Implicit dsl_fix [R].

Extraction Implicit  interp [ l r0 r1].
Extraction Implicit  interp_wrap [ r0 r1].

*)



Definition mytest := my_parse 1000 1 re1.


Extraction "../bench/lib/mytest" mytest.
Eval vm_compute in my_parse 5 1 re1.
Definition init_seq (len : nat) := nseq 





Fixpoint gen_strings n (r : @regex myFin) : option (seq myFin) := 
match n with 
| 0 => if r is Eps then Some nil else None 
| 1 => if r is Event a then (Some (a::nil)) else None
| n'.+1 =>
match r with 
| Eps => None 
| Empt => None 
| Event a => None 
| Plus r0 r1 => if gen_strings n' r0 is Some l then Some l else gen_strings n' r1
| Seq r0 r1 => if nu r0 then let l' := gen_strings n' r1 in
                            (compose (gen_strings n' r0) l' cat ) ++ l'
               else          (compose (gen_strings n' r0) (gen_strings n' r1 )cat )                                          
| Star r0 => gen_strings n' (Eps _+_ r0 _;_ (Star r0))
end
end.

Fixpoint gen_strings n (r : @regex myFin) : seq (seq myFin) := 
match n with 
| 0 => nil::nil
| n'.+1 =>
match r with 
| Eps => nil
| Empt => nil 
| Event a => (a::nil)::nil
| Plus r0 r1 => (gen_strings n' r0) ++ (gen_strings n' r1)
| Seq r0 r1 => if nu r0 then let l' := gen_strings n' r1 in
                            (compose (gen_strings n' r0) l' cat ) ++ l'
               else          (compose (gen_strings n' r0) (gen_strings n' r1 )cat )                                          
| Star r0 => gen_strings n' (Eps _+_ r0 _;_ (Star r0))
end
end.


(*Fixpoint enum2 (A  B: Type) (f : seq A -> option B)  (n : nat) (R : seq A) := 
match n with 
| 0 => f nil
| n'.+1 => seq_first 
 if seq_first f (compose R (enum n' R) cons) is Some l then l
          else nil
end.*)


Definition gen_tree (n : Decimal.signed_int) (r : @regex myFin) :=
if Nat.of_int n is Some n'
then  seq_first (fun l => parse l r)  (gen_strings n' r) else None.





Extraction "../bench/temp/suiteone" suiteone.


(*Extraction interp_wrap. Extraction interp.
Eval vm_compute in (synth_coercion re1 re2).
Print dsl.

Definition my_size  (r0 r1 : @regex myFin) (d : dsl nil r0 r1) := Nat.to_int (dsl_size d).


Definition example (Af : finType) (a : Af) : dsl nil (Star (Eps _+_ (Event a))) (Star (Event a)). 
apply :dsl_fix.
apply:ctrans. 
apply:drop. apply:cplus. apply:cid. apply:cid.
apply:ctrans. 2: { apply:wrap. } 
apply:cplus. apply:cid.
apply:dsl_var. done.
Defined.

Definition my_example := example myFin ord0.
Definition suitetwo := (test1,eval_test,@my_size,my_example).



Extraction "../bench/lib/suitetwo" suitetwo. 



Extraction "../bench/lib/my_test" my_test.


Extraction "../bench/lib/gen_tree" gen_tree.

Extraction "../bench/lib/strings_upto" strings_upto.
Eval vm_compute in (strings_upto 2).

Fixpoint gen_string (n : nat) (r : @regex myFin) := 
seq_first (fun x => derive x r) (index_enum myFin)
match n with 
| 0 => Some nil 
| n'.+1 => match r with 
          | Eps => None 
          | Empt => None 
          | Event


Definition gen_tree  (n : nat) (r : @regex myFin) : option (pTree r) :=
seq_first (fun p => n == pTree_0size p) (gen_trees (n + n) r).




(*Extraction Inline Equality.sort.
Extraction Inline Equality.sort Finite.sort Finite.class.*)




Definition ord0 : ordinal 2.
econ. instantiate (1:= 0). done.
Defined.

Eval vm_compute in (gen_trees 1 re_star).

Eval vm_compute in (gen_tree 1 re_star).

Print finType. Print Finite.type.
Definition A := ordinal 10.
(*What is the difference between extraction @synth_coercion, @synth_cercion A and Eval vm_compute in (@synth_coercion A)*)

(*One of the triplets is slow to reduce*)



Definition triple := (@synth_coercion,@gen_trees,@interp).
Definition tripleA_aux := (@synth_coercion A,@gen_trees A,@interp A).
Definition tripleA := Eval hnf in tripleA_aux.
Extraction "../bench/lib/triple" triple.
Extraction "../bench/lib/tripleA" tripleA.

(*Definition triple2 := Eval hnf in triple. 

Definition EventT := @Event Datatypes_nat__canonical__eqtype_Equality.

Definition Event2 := Eval vm_compute  in EventT.
Print eqType. Print Equality.type.
Recursive Extraction Event2.
Extraction "../bench/lib/event2" Event2.
Inductive TestT (A : eqType) := 
 T2 : A -> TestT A.

Extraction "../bench/lib/testT" TestT.

Definition nat_eq (n0 n1: nat) : n0 == n1.*)


Definition TestT2 := TestT Datatypes_nat__canonical__eqtype_Equality. 
Definition Test3 := Eval vm_compute in TestT2.
Extraction "../bench/lib/testT3" Test3.


Extraction "../bench/lib/mynat" nat_eq.
Extraction "../bench/lib/myregex" regex.regex.
Print regex.
Recursive Extraction triple.
Extraction "../bench/lib/triple2" triple2.




Extraction Inline solution_left.
Extraction Inline solution_right.
Extraction Inline simplification_heq.
Extraction Inline pTree_0size_rect.
Extraction Inline pTree_1size_rect.
Extraction Inline pTree_case.

(*Extraction Implicit p_pair [ A r0 r1].
Extraction Implicit p_inl [ A r0 r1].
Extraction Implicit p_inr [ A r0 r1].
Extraction Implicit p_fold [ A r ].
*)
Extraction synth_coercion.



(*Extraction Implicit shuffle [R A B C].
Extraction Implicit shuffleinv [R A B C].
Extraction Implicit retag [R A B].
Extraction Implicit untagL [R A].
Extraction Implicit untagLinv [R A].
Extraction Implicit untag [R A].
Extraction Implicit tagL [R A B].
Extraction Implicit assoc [R A B C].
Extraction Implicit associnv [R A B C].
Extraction Implicit swap [R A].
Extraction Implicit swapinv [R A].
Extraction Implicit proj [R A].
Extraction Implicit projinv [R A].
Extraction Implicit abortR [R A].
Extraction Implicit abortRinv [R A].
Extraction Implicit abortL [R A].
Extraction Implicit abortLinv [R A].
Extraction Implicit distL [R A B C].
Extraction Implicit distLinv [R A B C].
Extraction Implicit distR [R A B C].
Extraction Implicit distRinv [R A B C].
Extraction Implicit wrap [R A]. 
Extraction Implicit wrapinv [R A].
Extraction Implicit drop [R A B].
Extraction Implicit dropinv [R A B].
Extraction Implicit cid [R A].
Extraction Implicit ctrans [R A B C].
Extraction Implicit cplus [R A A' B B'].
Extraction Implicit cseq [R A  A' B B' ].
Extraction Implicit dsl_var [R].
Extraction Implicit dsl_fix [R].

Extraction Implicit  interp [ l r0 r1].*)

(*Extraction Implicit eq_op [ s].*)
(*Extraction Inline eq_op.*)
(*Extraction Inline Equality.eqtype_hasDecEq_mixin.
Print Equality.eqtype_hasDecEq_mixin.
Print Equality.axioms.
Locate Equality.
Print  mathcomp.ssreflect.eqtype.Equality.
Extraction Equality.axioms_.
Extraction hasDecEq.eq_op.
Extraction Finite.Exports.fintype_Finite__to__eqtype_Equality.*)
(*Extraction Inline Datatypes_prod__canonical__eqtype_Equality.
Extraction Inline regex_regex__canonical__eqtype_Equality.
(*Extraction Implicit pTree_1size_rect [ r P].
Extraction Inline pTree_1size_rect.
Extraction Implicit pTree_0size_rect [ r P].
Extraction Inline pTree_0size_rect.*)

Extraction Inline Datatypes_prod__canonical__eqtype_Equality.
Extraction Inline regex_regex__canonical__eqtype_Equality.

Extraction Inline  hasDecEq.phant_axioms. 
Extraction Inline Equality.eqtype_hasDecEq_mixin.
Extraction Inline hasDecEq.eq_op.
Extraction Inline Finite.Exports.fintype_Finite__to__eqtype_Equality.
Extraction Inline Finite.Exports.fintype_Finite_class__to__eqtype_Equality_class.

Extraction Inline Finite.eqtype_hasDecEq_mixin.
Extraction Inline fintype_ordinal__canonical__fintype_Finite.
Extraction Inline Equality.sort.*)
(*Recursive Extraction pTree.pTree.*)

(*Extraction Implicit  interp [ l r0 r1].*)
Extraction Inline eq_rect_r.
Extraction Inline eq_rect.
Extraction Inline Datatypes_nat__canonical__choice_Countable.
Extraction Inline unlock. Print regex.
Extraction Inline Equality.sort Finite.sort Finite.class.
Recursive Extraction triple. Locate fin. 

Extraction "../bench/lib/triple" triple.
*)
