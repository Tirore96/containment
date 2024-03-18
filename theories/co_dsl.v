
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

Inductive dslF (R: @regex Af -> @regex Af -> Type) : @regex Af -> @regex Af -> Type := 
| shuffle A B C : dslF R ((A _+_ B) _+_ C) (A _+_ (B _+_ C))
| shuffleinv A B C : dslF R (A _+_ (B _+_ C)) ((A _+_ B) _+_ C)
| retag A B: dslF R (A _+_ B) (B _+_ A)
| untagL A : dslF R (Empt _+_ A) A
| untagLinv A: dslF R A  (Empt _+_ A)
| untag A : dslF R (A _+_ A)  A
| tagL A B : dslF R A  (A _+_ B )

| assoc A B C : dslF R ((A _;_ B) _;_ C)  (A _;_ (B _;_ C)) 
| associnv A B C : dslF R (A _;_ (B _;_ C))   ((A _;_ B) _;_ C)

| swap A :  dslF R (A _;_ Eps)  (Eps _;_ A) 
| swapinv A : dslF R(Eps _;_ A)  (A _;_ Eps) 

| proj A : dslF R (Eps _;_ A)  A 
| projinv A : dslF R A (Eps _;_ A) 

| abortR A : dslF R (A _;_ Empt)  Empt 
| abortRinv A : dslF R Empt   (A _;_ Empt) 

| abortL A : dslF R (Empt _;_ A)   Empt 
| abortLinv A : dslF R Empt    (Empt _;_ A)

| distL A B C : dslF R (A _;_ (B _+_ C))  ((A _;_ B) _+_ (A _;_ C))
| distLinv A B C : dslF R  ((A _;_ B) _+_ (A _;_ C)) (A _;_ (B _+_ C))

| distR A B C : dslF R ((A _+_ B) _;_ C)  ((A _;_ C) _+_ (B _;_ C))
| distRinv A B C : dslF R ((A _;_ C) _+_ (B _;_ C))   ((A _+_ B) _;_ C)

| wrap A : dslF R (Eps _+_ (A _;_ Star A))  (Star A)
| wrapinv A : dslF R (Star A)  (Eps _+_ (A _;_ Star A))

| drop A B : dslF R A (Eps _+_ B) -> dslF R (Star A)  (Eps _+_ B _;_ Star ( A))

(*| drop A : dslF R  (Star (Eps _+_ A))  (Star A)*)
(*| dropinv A : dslF R (Star A)  (Star (Eps _+_ A)) *)
| cid A : dslF R A A 

(*| ci_sym A B (H: A =R=B) : B =R=A*)
| ctrans A B C  : dslF R  A B ->  dslF R B C -> dslF R A C
| cplus A A' B B'  : dslF R A A'  -> dslF R B B' -> dslF R  (A _+_ B) (A' _+_ B')
| cseq A A' B B'  : dslF R A A' -> dslF R B B' ->  dslF R (A _;_ B) (A' _;_ B')
| cstar A B: dslF R  A B -> dslF R (Star A)  (Star B)
(*| cfix r r' (p  : dslF R dslF) : dslF R r  r' p[d (cfix p) .: dslF R var_dslF] ->  r  r' (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dslF R ((Event a) _;_ A)  ((Event a) _;_ B)*)

(*We need this to be a sum because Coq disallows fix in cofix*)
| guard l F F' : (forall a, a \in l -> R (F a) (F' a))  -> dslF R (\big[Plus/Empt]_(a <- l) ((Event a) _;_ F a))
                                                           (\big[Plus/Empt]_(a <- l) ((Event a) _;_ F' a)).
(**)


CoInductive dsl_co : regex -> regex -> Type := 
| Co_fold A B : dslF dsl_co A B -> dsl_co A B.
Hint Constructors dsl_co.

Notation "c0 < ⟨ R ⟩ = c1" := (dslF R c0 c1)(at level 63).

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
Arguments drop {R A B}.
(*Arguments dropinv {R A}.*)
Arguments cid {R A}.
Arguments ctrans {R A B C}.
Arguments cplus {R A A' B B'}.
Arguments cseq {R A A' B B'}.
Arguments cstar {R A B}.
Hint Constructors dslF.

Section Interpret.
Fixpoint interp l r0 r1 (p : dslF l r0 r1) (T : pTree r0) 
         (f : forall x y,  l x y -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) {struct p}:
  post r1 T. 
refine(
match p in dslF _ x y return r0 = x -> r1 = y -> post r1 T  with
| guard l r0 r1 p0 => fun HQ HQ' => _ (*Do at least one case to force coq to destruct *)
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


(*One-size induction*)
move: T f. apply: pTree_1size_rect.
intros. dp2 u X f. dp2 p X f. 
 - dp2 p X f.
exists ((p_inl p_tt))=>//=.
-
dp2 p X f.
have: (forall x y : regex_regex__canonical__eqtype_Equality Af,
     l x y -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).  
intros. apply f. done. 
move: H. rewrite /pRel0 /=. lia.
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
    l x y -> forall T0 : pTree x, pRel0 T0 p1 -> post y T0).
intros. apply f. done.
move : H. rewrite /pRel0.  ssa. lia. move=>Hf2.
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


(*clear f interp.
move: T. apply: pTree_1size_rect.
intros. dp u X. dp p X. dp p X.
exists (p_fold (p_inl p_tt))=>//=.
dp p X. 
dp p0 X. dp p X.
move: (X p1)=>/=. rewrite /pRel1 /=.
have: pTree_1size p1 < 1 + pTree_1size p1. lia. 
move=>Hsize. move/(_ Hsize). case=>x Hx.
exists x. ssa. 
move: (X p1)=>/=. rewrite /pRel1 /=.
have: pTree_1size p1 < pTree_1size p + pTree_1size p1. move: (pTree_1size1 p). lia.
move=>Hsize. move/(_ Hsize). case=>x Hx.
exists (p_fold (p_inr (p_pair p x))). ssa. lia. rewrite H0//.*)

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

exists T. ssa.

case: (interp _ _ _ d T f)=> T' HT'. 
have:  (forall x y ,
         l x y -> forall T0 : pTree x, pRel0 T0 T' -> post y T0).
intros. eapply f. eauto. move: H. rewrite /pRel0. ssa. lia. move=>Hf. 
case: (interp _ _ _ d0 T' Hf)=>T2 HT2.  
exists T2. ssa. lia. rewrite H2 H0 //.

move: (interp _ _ _ d)=>H0.  
move: (interp _ _ _ d0)=>H1.  

dp T f. 
have: (forall x y, l x y -> forall T0 : pTree x, pRel0 T0 p -> post y T0).
intros. eapply f. eauto. done. 
move=>Hf0. 
case: (H0 p Hf0)=>T0 HT0.  
exists (p_inl T0)=>//. 

have: (forall x y, l x y -> forall T0 : pTree x, pRel0 T0 p -> post y T0).
intros. eapply f. eauto. done. move=>Hf.
case: (H1 p Hf)=>T1 HT1. 
exists (p_inr T1)=>//. 

move: (interp _ _ _ d)=>H0.
move: (interp _ _ _ d0)=>H1. 
dp T f.
have: (forall x y,   l x y  -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).
intros. eapply f. eauto. move: H. rewrite /pRel0 //=. lia. move=>Hf0.
have: (forall x y, l x y -> forall T0 : pTree x, pRel0 T0 p1 -> post y T0).
intros. eapply f. eauto. move: H. rewrite /pRel0 //=. lia. move=>Hf1.

case: (H0 p0 Hf0) =>T0' HT0'.
case: (H1 p1 Hf1) =>T1' HT1'.
exists (p_pair T0' T1')=>//=. ssa. lia. rewrite H4 H2 //. 


move: (interp _ _ _ d) f. 
(*One-size induction*)
clear interp d. 
move: T. apply: pTree_1size_rect.
intros. dp2 u f X. dp2 p f X. dp2 p f X.
exists (p_fold (p_inl p_tt))=>//=.
dp2 p f X. 
have: (forall x y, l x y -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).
intros. eapply f. eauto. move: H. rewrite /pRel0 //=. lia. 
move=>Hf.
case: (interp p0 Hf)=> x Hx. 
have: pRel1 p1 (p_fold (p_inr (p_pair p0 p1))). rewrite /pRel1 //=. move: (pTree_1size1 p0). lia.
move=>Hsize.
have: (forall x0 y,
    l x0 y -> forall T0 : pTree x0, pRel0 T0 p1 -> post y T0).
intros. eapply f. eauto. move: H. rewrite /pRel0 /=.  lia.
move=>Hf'.
case: (X p1 Hsize interp Hf')=>x' Hx'. 
exists (p_fold (p_inr (p_pair x x'))). ssa. lia. rewrite H0 H2//.
clear interp.
have: forall a, a \in l ->  forall T0 : pTree (r0 a), pRel0 T0 T -> post (r1 a) T0.
intros. apply f.  apply p0. done. done.  clear f p0=> f.
move : l T f. elim.
ssa. exfalso. clear f. rewrite big_nil in T. inv T.
intros.
move: T f. 
simpl. rewrite !big_cons.
intros.
dp T f. dp p f. dp p0 f.
have: post (r1 a) p1. 
apply:f. done. rewrite /pRel0. ssa.
case. ssa.  exists ((p_inl (p_pair (p_singl a) x))). ssa. rewrite H0 //.
have: (forall a0 : Af, a0 \in l -> forall T0 : pTree (r0 a0), pRel0 T0 p -> post (r1 a0) T0).
intros. apply f. rewrite !inE H. lia. done.
move=> f2.
move: (X p f2).
case. ssa.
exists (p_inr x). ssa.
Defined.

(*Custom Acc because our type index changes over time*) 
Inductive Acc2  (r : regex) (T : pTree r) : Prop :=  Acc2_intro : (forall r' (T' : pTree r'), @pRel0 Af _ _ T' T -> Acc2  T') -> Acc2 T.

Lemma pTree_0size_rect
     : forall P : forall r, pTree r -> Type,
       (forall r (u  : pTree r), (forall r' (u' : pTree r'), @pRel0 Af _ _ u' u -> P _ u') -> P _ u) ->
       forall r (p : pTree r), P r p.
Proof.
move=> P  Hsize r u. 
have: Acc2 u. 
clear Hsize. 
move Heq : (pTree_0size u)=>n. move: n Heq.
suff : forall n : nat, pTree_0size u <= n -> Acc2 u.
intros. eauto.
move=>n. move: n r u.
elim.
intros. con. intros. rewrite /pRel0 in H0. lia.
intros. con. intros. apply/H. rewrite /pRel0 in H1. lia.
move=>Hacc.
move: r u Hacc Hsize. apply: Acc2_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.


(*Lemma pTree_0size_rect2
     : forall (P : forall r, pTree r -> Type),
       (forall r (u  : pTree r), (forall r' (u' : pTree r'), pRel0 u' u -> P _ u') -> P _ u) ->
       forall r (p : pTree r), P r p.
Proof.
move=> P  Hsize r u. 
have: Acc pRel0 u. clear Hsize. 
move Heq : (pTree_0size u)=>n. move: n Heq. 
suff : forall n : nat, pTree_0size u <= n -> Acc (fun p' p  => pRel0 p' p) u.
intros. eauto.
move=>n. elim: n u.
intros. con. intros. rewrite /pRel0 in H0. lia.
intros. con. intros. apply/H. rewrite /pRel0 in H1. lia.
move=>Hacc.
move: u Hacc Hsize. 
apply: Acc_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.*)

Definition interp_wrap2 r0 r1 (p : dsl_co r0 r1) (T : pTree r0) : post r1 T. 
move: r0 T r1 p.
apply:(@pTree_0size_rect (fun r0 (T : pTree r0) => forall r1, dsl_co r0 r1 -> post r1 T)).
intros. destruct X0.
eapply interp. apply d. 
intros.  apply X. done. done.
Qed.


Lemma dsl_sound : forall c0 c1, dsl_co c0 c1 -> (forall s, Match s c0 -> Match s c1).
Proof.
move=> c0 c1 d s Hmatch. 
case: (exists_pTree Hmatch) => x /eqP Hf. subst.
case: (interp_wrap2 d x). ssa. rewrite H0.
rewrite -uflatten_to_upTree.
apply pTree_Match. apply:to_typing.
Qed.


(*Extraction Inline  solution_left.
Extraction Inline  solution_right.
Extraction Inline  simplification_heq.
Extraction Inline pTree_0size_rect.
Extraction Inline pTree_1size_rect.
Extraction Inline pTree_case.
Extraction Implicit interp [ 3 4].
Extraction Implicit p_pair [ 1].

Extraction interp.
Extraction pTree_case.*)

End Interpret.





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

Lemma o_seq_l : forall c0 c1 R,  o (c0 _;_ c1) <⟨R⟩= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.

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

Lemma eps_c_r : forall r R,   r < ⟨R⟩= r _;_ Eps.
Proof.
intros. econ. lct2. apply:swapinv. eauto. done. done.
Qed.

Hint Resolve eps_c_r.

Lemma eps_c_l : forall r R,   r _;_ Eps < ⟨R⟩= r .
Proof.
intros. econ. lct1. apply:swap. eauto. eauto.
Qed.

Hint Resolve eps_c_l.

Definition ex_coerce (l: seq Af) (F0 F1 : Af -> @regex Af) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus_c : forall (l : seq Af) F1 F2 R, ex_coerce l F1 F2 (dslF R) ->
   \big[Plus/Empt]_(i <- l) (F1 i) <⟨R⟩= \big[Plus/Empt]_(i <- l) (F2 i). 
Proof.
move=> + F1 F2 R. 
rewrite /ex_coerce. elim=>//.
move=> _. rewrite !big_nil//. 
move=> a l IH Hin. rewrite !big_cons /=. lcp1. apply:Hin. done.
eauto. 
Qed.

Lemma derive_seq_l : forall R a r r', a \ (r _;_ r') <⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') .
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /=. 
lcp1. lcid. eauto. 
rewrite /o Hcase /=.  eauto.
Qed.

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

(*Uses drop!*)
(*Lemma star_o_l : forall R c c', Star (o (c) _+_ c') <⟨R⟩ = Star c' .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.*)

(*Lemma star_o_r : forall R c c', Star c' <⟨R⟩ =  Star (o (c) _+_ c') .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.*)
Check dslF.
Lemma derive_unfold_coerce_l : forall ( l : regex -> regex -> Type)c , dslF l  c (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)).
Proof. 
move=>l.
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



Lemma dropinv R A B : dslF R (Eps _+_ B) A -> dslF R  (Eps _+_ B _;_ Star ( A)) (Star A). 
Proof.
intros. apply:ctrans. apply:cplus. apply:cid. apply:cseq.
apply:ctrans. apply:tagL. apply: Eps. 
apply:ctrans. apply:retag.  apply:X. apply:cid.
apply:wrap.
Qed.


Lemma derive_unfold_coerce_r : forall l c, dslF l (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)) c.
Proof.
move=> l.
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





(*Lemma derive_unfold_coerce_l : forall R c,  dslF R c (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)). 
Proof.
intros. destruct (derive_unfold_coerce R c). done.
Qed.

Lemma derive_unfold_coerce_r : forall R c, dslF R (o c _+_ \big[Plus/Empt]_(a : Af) (Event a _;_ a \ c)) c.
Proof.
intros. destruct (derive_unfold_coerce R c). done.
Qed.*)



Lemma nu_imp_coerce_aux : forall R r0 r1, (nu r0 -> nu r1) ->  o r0 <⟨R⟩= o r1. 
Proof.
intros. destruct (nu r0) eqn:Heqn. rewrite /o Heqn H //. econ. lcid. 
rewrite /o Heqn.
destruct (nu r1). econ.
lct2. apply:untagL.
apply:tagL.
eauto. done.
Qed.



Definition check_o := (fun ( l0 l1 : @pder Af) => has nu l0 ==> has nu l1).


Inductive bisimilarity_gen bisim : @regex Af -> regex -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: check_o [::c0] [::c1]) : bisimilarity_gen bisim c0 c1.

Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.

Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve bisimilarity_gen_mon : paco.

(*Lemma bisim_soundness : forall (c0 c1 : regex), EQ c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. 
intros. pfold. constructor.
- intros. right. apply CIH.  apply co_eq_derive. auto.
- rewrite /Pb /=. do 2 rewrite orbC /=.  apply/eqP. auto using co_eq_nu.
Qed.
*)
(*Theorem equiv_r2 : forall c0 c1, Bisimilarity c0 c1 -> equiv_r c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. rewrite /Pb in HC'. 
  move/eqP: HC'=>HC'. ssa. do 2 rewrite orbC //= in HC'.
  rewrite !matchbP /matchb /= HC' //.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.*)

Theorem contains_r1 : forall c0 c1, contains_r c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  rewrite /contains_r. move=> s.  rewrite -!deriveP. eauto.
  move: (H0 nil). rewrite !matchbP /matchb /=.  
  intros. apply/implyP. ssa. rewrite orbC /= in H. auto.
Qed.

Lemma bisim_nu : forall c0 c1, Bisimilarity c0 c1 -> nu c0 -> nu c1.
Proof.
intros. 
have:  bisimilarity_gen (upaco2 bisimilarity_gen bot2) c0 c1. punfold H.
clear H=> H. destruct H. ssa.  rewrite /check_o in H2. ssa.
rewrite orbC /= in H2. 
suff : nu c1 || false. rewrite orbC //=. 
apply (implyP H2). done.
Qed.

Lemma Empt_r : forall L r, Empt < ⟨ L ⟩ = r.
Proof.
intros. lct1. apply:tagL. 2: { lct1. apply:retag. eauto. } 
Qed.


Lemma bisim_o : forall R c0 c1, Bisimilarity c0 c1 -> dslF R (o c0) (o c1).
Proof.
intros.
move: (bisim_nu H)=>HH. rewrite /o.
destruct (nu _) eqn:Heqn. rewrite HH //. 
case_if;ssa.  apply Empt_r.
Qed.

Lemma bisim_proj : forall c0 c1, Bisimilarity c0 c1 -> (forall a, Bisimilarity (a \ c0) (a \ c1)).
Proof.
intros. punfold H. inv H. destruct (H0 a). apply H2. done.
Qed.

Lemma nu_coerce : forall r0 r1 (H: nu r0 -> nu r1), dslF dsl_co (o r0) (o r1).
Proof.
intros.
rewrite /o. destruct (nu _)eqn:Heqn. rewrite H. con. done.
destruct (nu r1) eqn:Heq. apply:ctrans. 2: apply:untagL. apply:tagL.
con.
Qed.

(*To convice guardedness checker, we use the actual ctrans constructor and not 
  the derived ctrans1/ctrans2 *)
Lemma bisim_dsl_co : forall c0 c1, Bisimilarity c0 c1 -> dsl_co c0 c1.
Proof.
cofix CIH. 
intros. con. 
move: (bisim_nu H) (bisim_proj H)=>HH HH2.
apply:ctrans. apply:derive_unfold_coerce_l.
apply:ctrans.  2: apply:derive_unfold_coerce_r.
apply:cplus. apply nu_coerce. apply HH.
clear HH.
apply:guard.
intros. apply:CIH. apply:HH2.
Qed.


Lemma c_eq_completeness : forall (c0 c1 : regex), contains_r c0 c1 -> dsl_co c0 c1.
Proof. move=> c0 c1.
move/contains_r1.
move/bisim_dsl_co. 
done.
Qed.





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

Section Decidability.


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

Lemma synth_coercion : forall (r0 r1 : @regex Af), option (dsl_co r0 r1). 
Proof.
intros. 
destruct (enum.reachable_wrap [::r0] [::r1] check_o) eqn:Heqn.
move/P_decidable : Heqn. move=>HH. con. 
apply:c_eq_completeness.  apply/contains_seq1. done.
apply : None.
Qed.
End Decomposition.
End DSL.

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
Definition split_l {A : Type} (l : seq A) := map (fun n => (take n l,seq.drop n l)) (iota 0 (size l)).
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

Definition interp_wrap {r0 r1 : @regex myFin} (p : dsl_co r0 r1) (T : pTree r0) : post r1 T. 
move: r0 T r1 p.
apply:(@pTree_0size_rect _ (fun r0 (T : pTree r0) => forall r1, dsl_co r0 r1 -> post r1 T)).
intros. destruct X0.
eapply interp. apply d. 
intros.  apply X. done. done.
Qed.

(*Fixpoint dsl_size {l} {r0 r1 : @regex myFin} (d : dsl l r0 r1) : nat := 
match d with 
| ctrans _ _ _ d0 d1 => (dsl_size d0) + (dsl_size d1)
| cplus _ _ _ _ d0 d1 =>  (dsl_size d0) + (dsl_size d1)
| cseq _ _ _ _ d0 d1 =>  (dsl_size d0) + (dsl_size d1)
| dsl_fix _ _ d0 =>  (dsl_size d0)
| _ => 1
end.*)

Definition time_synth_coercion := @synth_coercion_wrap.
Definition time_interp_wrap := @interp_wrap.

Definition interp_size (r0 r1: @regex myFin) (prog : dsl_co r0 r1) := (fun T0 => (pTree_1size T0,proj1_sig (time_interp_wrap prog T0))).

Definition synth_interp (n : nat) (l : seq nat) (r0 r1 : @regex myFin): option (seq (nat * pTree r1)) :=
match time_synth_coercion r0 r1 with 
| Some prog => let Ts := pmap (fun x => my_parse n x r0) l
              in if size Ts != size l then None 
              else Some (map (@interp_size r0 r1 prog) Ts) (*(fun T0 => (pTree_1size T0,proj1_sig (time_interp_wrap prog T0))) Ts)*)
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
Definition tree_sizes : seq nat := [:: 50].

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


Extraction "../bench/lib/testsuitecoind" test.
