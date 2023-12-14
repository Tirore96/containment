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
From Containment Require Import  tactics utils regex pred modules constructiveEps.
Set Implicit Arguments.
Set Maximal Implicit Insertion.



Let inE := tactics.inE.


(*Module Type ContainerM.
Parameter (F : Type -> Type).
End ContainerM.*)

Module MyDSL (M : FModule).
Module CM := Constructive M.
Import M CM.
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
Set Printing Coercions.
Check dsl_var.
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


Section Interpret.

Fixpoint pTree_0size r  (p : pTree r) := 
match p with 
| p_tt => 0
| p_singl _ => 1
| p_inl _ _ p0 => pTree_0size p0
| p_inr _ _ p1 => pTree_0size p1
| p_pair  _ _ p0 p1 => (pTree_0size p0) + (pTree_0size p1)
| p_fold  _ p0 => (pTree_0size p0) 
end.

Fixpoint pTree_1size r  (p : pTree r) := 
match p with 
| p_tt => 1 
| p_singl _ => 1
| p_inl _ _ p0 => pTree_1size p0
| p_inr _ _ p1 => pTree_1size p1
| p_pair  _ _ p0 p1 => (pTree_1size p0) + (pTree_1size p1)
| p_fold  _ p0 => (pTree_1size p0) 
end.


Definition pRel (r : regex) (p' p : pTree r) := pTree_0size p' < pTree_0size p.
Definition pRel0 (r' r : regex) (p' : pTree r') (p : pTree r) := pTree_0size p' < pTree_0size p.
Definition pRel1 (r' r : regex) (p' : pTree r') (p : pTree r) := pTree_1size p' < pTree_1size p.



Lemma pTree_0size_rect
     : forall (r: regex) (P : pTree r -> Type),
       (forall (u  : pTree r), (forall u' : pTree r, pRel u' u -> P u') -> P u) ->
       forall (p : pTree r), P p.
Proof.
move=> r P  Hsize u. 
have: Acc pRel u. clear Hsize. 
move Heq : (pTree_0size u)=>n. move: n Heq.
suff : forall n : nat, pTree_0size u <= n -> Acc (fun p' p : pTree r => pRel p' p) u.
intros. eauto.
move=>n. elim: n u.
intros. con. intros. rewrite /pRel in H0. lia.
intros. con. intros. apply/H. rewrite /pRel in H1. lia.
move=>Hacc.
move: u Hacc Hsize. apply: Acc_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.

Lemma pTree_1size_rect
     : forall (r: regex) (P : pTree r -> Type),
       (forall (u  : pTree r), (forall u' : pTree r, pRel1 u' u -> P u') -> P u) ->
       forall (p : pTree r), P p.
Proof.
move=> r P  Hsize u. 
have: Acc pRel1 u. clear Hsize. 
move Heq : (pTree_1size u)=>n. move: Heq.
wlog: u n / pTree_1size u <= n. intros. apply/H. 2:eauto. lia.
move=> + _.
elim: n u.
intros. con. intros. rewrite /pRel1 in H0. lia.
intros. con. intros. apply/H. rewrite /pRel1 in H1. lia.
move=>Hacc.
move: u Hacc Hsize. apply: Acc_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.


Definition post (r0 r1 : regex) (T : pTree r0) := 
  { T' : pTree r1 | pTree_0size T' <= pTree_0size  T /\ pflatten T = pflatten T' }. 

Lemma pTree_0size0 : forall r (p : pTree r), pTree_0size p = 0 -> pflatten p = nil.
Proof.
move=> r.
elim;ssa. have: pTree_0size p = 0 by lia. move/H=>->/=. 
apply:H0. lia.
Qed.


Lemma pTree_1size1 : forall r (p : pTree r), 0 < pTree_1size p. 
Proof.
move=> r.
elim;ssa.  lia.
Qed.

Lemma pTree_false : forall r (p : pTree r), pTree_1size p <= 0 -> False. 
Proof.
intros. move: (pTree_1size1 p). lia.
Qed.

(* ala https://jamesrwilcox.com/dep-destruct.html*)
Lemma pTree_case : forall (r : regex) (P : pTree r -> Type), (forall (pf :  Eps = r), P (@eq_rect _ _ pTree p_tt _ pf)) -> 
                                                       (forall a (pf : Event a = r), P (@eq_rect _ _ pTree (p_singl a) _ pf)) -> 
                                                       (forall r0 r1 (pf : r0 _+_ r1 = r) (p : pTree r0), 
                                                           P (@eq_rect _ _ pTree (p_inl p) _ (pf))) -> 
                                                       (forall r0 r1 (pf : r0 _+_ r1 = r) (p : pTree r1), 
                                                           P (@eq_rect _ _ pTree (p_inr p) _ (pf))) -> 
                                                       (forall r0 r1 (pf :r0 _;_ r1 = r) (p0 : pTree r0)(p1: pTree r1), 
                                                           P (@eq_rect _ _ pTree (p_pair p0 p1) _ ( pf))) -> 
                                                       (forall r0  (pf : Star r0 = r) (p : pTree (Eps _+_ r0 _;_ Star r0)),
                                                           P (@eq_rect _ _ pTree (p_fold p) _ (pf))) -> 
                                                       (forall p, P p).
Proof.
intros.
destruct p eqn:?. 
move: (X Logic.eq_refl)=>//. 
move: (X0 a Logic.eq_refl)=>//=.
move: (X1 r0 r1 Logic.eq_refl p0)=>//=.
move: (X2 _ _ Logic.eq_refl p0)=>//.
move: (X3 _ _ Logic.eq_refl p0_1 p0_2)=>//.
move: (X4 _ Logic.eq_refl p0)=>//.
Qed.


Ltac dep_destruct p :=
  pattern p; apply pTree_case; clear p; intros;try discriminate.


Hint Constructors pTree : pTree.

Lemma regex_dec : forall (x y : @regex A), { x = y} + { x <> y }.
Proof. 
intros. de (eqVneq x y)=>//. constructor 2. apply/eqP=>//.
Qed.
Definition eq_regex r0 := @Eqdep_dec.eq_rect_eq_dec _ regex_dec r0 pTree.
Ltac inv_eq := match goal with 
                   | [H : _ = _ |- _] => inv H
                 end.
Ltac clear_eq := match goal with 
                   | [H : ?x = ?x |- _] => clear H
                 end.


Ltac dp T f := move: T f;apply:pTree_case=>//; intros; inv_eq; move:f; rewrite <- eq_regex;clear_eq=>f. 
Ltac dp2 T f f' := move: T f f';apply:pTree_case=>//; intros; inv_eq; move:f f'; rewrite <- eq_regex;clear_eq=>f f'. 
Fixpoint interp l r0 r1 (p : dsl l r0 r1) (T : pTree r0) 
         (f : forall x y,  (x,y) \in l -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) {struct p}:
  post r1 T. 
refine(
match p in dsl _ x y return r0 = x -> r1 = y -> post r1 T  with
| dsl_fix r0 r1 p0 => fun HQ HQ' => _ (*Do at least one case to force coq to destruct *)
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
all:clear p;intros;subst.
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
clear f interp.
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
exists (p_fold (p_inr (p_pair p x))). ssa. lia. rewrite H0//.

(*One-size induction*)
clear f interp.
move: T. apply: pTree_1size_rect.
intros. dp u X. dp p X. dp p X.
exists (p_fold (p_inl p_tt))=>//=.
dp p X. 
move: (X p1)=>/=. rewrite /pRel1 /=.
have: pTree_1size p1 < pTree_1size p0 + pTree_1size p1.  move:(pTree_1size1 p0). lia.
move=>Hsize. move/(_ Hsize). case=>x Hx.
exists (p_fold (p_inr (p_pair (p_inr p0) x))). ssa. lia. rewrite H0//.

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


move: (interp _ _ _ d) f. 
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
exists (p_fold (p_inr (p_pair x x'))). ssa. lia. rewrite H0 H2//.

dp T f. dp p0 f. 
have : pRel0 p1 (p_pair (p_singl s) p1). rewrite /pRel0 /=. lia.
move=>Hrel.
move: (f s0 s1 i p1 Hrel).
case. move=> x Hflat. ssa. 
exists (p_pair (p_singl s) x). 
ssa. f_equal. done. 

move : T f.
eapply (@pTree_0size_rect r0 (fun (T : pTree r0) => (forall x y,(x,y) \in l -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) -> post r1 T)).
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
case. intros. ssa. rewrite H0. rewrite -uflatten_to_upTree.
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





Section DSL_Complete.

(*Lemma unf0 d : mu_height d = 0 -> full_unf d = d. 
Proof.
rewrite /full_unf. move=>->//. 
Qed.
Ltac t0 := exact:unf0.

Hint Resolve unf0.*)



(*Definition proj_proof {A : Type} {P : A -> Prop}  (H : { x| P x}) : P (proj_sig H)  :=
match H with 
| exist x H => H
end.*)
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




(*Inductive contains2_gen bisim : regex -> regex -> Prop :=
 contains2_con c0 c1 (H0: Forall (fun e => bisim (e \ c0) (e \ c1)) (index_enum A)) (H1: nu c0 -> nu c1) : contains2_gen bisim c0 c1.


Lemma contains2_gen_mon: monotone2 contains2_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. 
elim: H0;ssa. inv IN.
Qed.
Hint Resolve contains2_gen_mon : paco.*)



(*Definition Contains2 r0 r1 := paco2 contains2_gen bot2 r0 r1.

Lemma Contains2_der : forall c0 c1, Contains c0 c1 -> Forall (fun e => Contains2 (e \ c0) (e \ c1)) (index_enum A).
Proof.
intros. punfold H.  inv H. 
clear H. elim:H0;ssa. con. inv H.  done.
Qed.


Lemma Contains2_nu : forall c0 c1, Contains2 c0 c1 ->  nu ( c0) -> nu ( c1).
Proof.
intros. punfold H.  inv H. eauto. 
Qed.

*)


(*Definition contains c c' := forall s, Match s c -> Match s c'.*)

Lemma contains_derive : forall c c' e, contains c c' -> contains (e \ c) (e \ c').  
Proof.
move => c c' e. rewrite /equiv. move=> HM s. rewrite -!deriveP. apply/HM.
Qed.


Inductive contains_gen bisim : regex -> regex -> Prop :=
 contains_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: nu c0 -> nu c1) : contains_gen bisim c0 c1.



Definition Contains c0 c1 := paco2 contains_gen bot2 c0 c1.
Hint Unfold  Contains : core.

Lemma contains_gen_mon: monotone2 contains_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve contains_gen_mon : paco.


Theorem contains1 : forall c0 c1, contains c0 c1 -> Contains c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  apply/contains_derive=>//.
- move=>Hnu. have: Match nil c0. apply/Match_nil_nu=>//.
  move/H0. move/nuP=>//. 
Qed.



Theorem contains2 : forall c0 c1, Contains c0 c1 -> contains c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC Hnu HC'. apply/nuP/Hnu/nuP=>//.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.


Theorem containsP : forall c0 c1, contains c0 c1 <-> Contains c0 c1.
Proof.
move=> c0 c1. con. apply/contains1. apply/contains2.
Qed.




Hint Resolve undup_uniq.
Unset Implicit Arguments.

(*Less effecient, fix this later*)
Equations containsb (pp : pder * pder) (visited : seq (pder * pder) ) : bool by wf (r_measure visited pp) := 
 containsb pp visited  with (dec (pp \in visited)) => {
  containsb _  _ (in_left) := true;
  containsb pp visited (in_right) with (dec (uniq_pair pp)) => { 
        containsb pp visited _ (in_left) := ((has nu pp.1) ==> (has nu pp.2)) && 
                                        (foldInAll (index_enum A) (fun e _ => containsb (pair_pd_l e (pp)) (pp::visited)));
        containsb pp visited _ (in_right) := false }
 }.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.

(*Effecient but awkard for proofs*)
Equations containsb2 (pp : pder * pder) (visited : seq (pder * pder) ) (H : uniq_pair pp) : bool by wf (r_measure visited pp) := 
 containsb2 pp visited H  with (dec (pp \in visited)) => {
  containsb2 _  _ _ (in_left) := true;
  containsb2 pp visited _ (in_right) := ((has nu pp.1) ==> (has nu pp.2)) && 
                                           (foldInAll (index_enum A) (fun e _ => containsb2 (pair_pd_l e pp) (pp::visited) _));
 }.
Next Obligation. 
apply/andP.
con. simpl. rewrite /pd_l. done.  simpl. rewrite /pd_l. done.
Defined.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.
Set Implicit Arguments.

Lemma containsb12 : forall pp visited (H : uniq_pair pp), containsb pp visited -> containsb2 pp visited H.
Proof.
intros. funelim (containsb pp visited).
simp containsb2. simpl. rewrite Heq. simpl. done.
simp containsb2. rewrite Heq0. simpl.
rewrite -Heqcall in H1. ssa.
rewrite !foldInAllP in H3 *. 
apply/allP. intro. intros. move: (allP H3 _ H1). move/H. move/inP: H1=>H1'. move/(_ H1')=>Hall.
apply Hall. rewrite -Heqcall in H0. done.
Qed.

Lemma containsb21 : forall pp visited (H : uniq_pair pp), containsb2 pp visited H -> containsb pp visited.
Proof.
intros. funelim (containsb pp visited). rewrite -Heqcall. done.
rewrite -Heqcall. simp containsb2 in H1. rewrite Heq0 in H1. ssa.
rewrite !foldInAllP in H3 *. 
apply/allP. intro. intros. move: (allP H3 _ H1). move/H. move/inP: H1=>H1'. move/(_ H1')=>Hall.
apply Hall.  clear H0.
rewrite e1 in H. done.
Qed.

Lemma containsb_iff : forall pp visited (H : uniq_pair pp), containsb pp visited <-> containsb2 pp visited H.
Proof.
intros. split. apply:containsb12. apply:containsb21.
Qed.

Inductive contains_ind_gen contains : pder -> pder-> Prop :=
 contains_con3 l0 l1 (H0: forall e, contains (pd_l e l0) (pd_l e l1) : Prop ) (H1: has nu l0 -> has nu l1) : contains_ind_gen contains l0 l1.

Definition ContainsInd l0 l1 := paco2 contains_ind_gen bot2 l0 l1.
Hint Unfold  ContainsInd : core.

Lemma contains_ind_gen_mon: monotone2 contains_ind_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve contains_ind_gen_mon : paco.

Lemma containsb_complete_aux : forall l0 l1 l_v, uniq_pair (l0,l1) ->  ContainsInd l0 l1 ->  containsb  (l0,l1) l_v. 
Proof. 
intros. funelim (containsb  (l0,l1) l_v).  rewrite -Heqcall. ssa.
rewrite -Heqcall. ssa. 
punfold H1.  inv H1. apply/eqP=>//. apply/eqP. apply/implyP. done.
rewrite foldInAllP. apply/allP=> x xIn. 
apply:H. apply/inP. eauto.  simpl. 
rewrite /uniq_pair /pd_l. ssa.
punfold H1. inv H1. case: (H2 x)=>//. con. 
done. rewrite  e1 in H. done.
Qed.


Definition containsb_wrap (l l' : pder) := containsb (undup l,undup l') nil.

Theorem equiv_rInd2 : forall l l', ContainsInd l l' -> contains ( (\big[Plus/Empt]_(i <- l) i))  (\big[Plus/Empt]_(i <- l') i).
Proof.
move=> l0 l1 HC s. 
elim: s l0 l1  HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. intros. apply/Match_has_nu_iff/HC'/Match_has_nu_iff.  done.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. 
  rewrite !deriveP2. rewrite /pd_sum. rewrite !pd_plus //.
  apply/IH=>//. 
Qed.

Lemma derive_pd_l2 : forall l e, contains (e \ \big[Plus/Empt]_(i <- l) i) 
                                   (\big[Plus/Empt]_(i <- pd_l e l) i).
Proof.
intros. intro.  move: (derive_pd_l l e s). case. ssa.
Qed.

Lemma derive_pd_l3 : forall l e, contains  (\big[Plus/Empt]_(i <- pd_l e l) i)  (e \ \big[Plus/Empt]_(i <- l) i) .
Proof.
intros. intro.  move: (derive_pd_l l e s). case. ssa.
Qed.

Lemma contains_r_trans : forall r0 r1 r2, contains r0 r1 -> contains r1 r2 -> contains r0 r2.
Proof.
intros. intro. eauto. 
Qed.

Theorem Contains_co_ind : forall l l', Contains (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i) -> ContainsInd l l'.
Proof.
pcofix CIH. intros. punfold H0. inv H0. pfold. con. intros.
right. apply/CIH. 
destruct (H1 e)=>//. apply/containsP. move/containsP : H.
intros. 
apply/contains_r_trans.
apply:derive_pd_l3.
apply/contains_r_trans.
2: { apply:derive_pd_l2. } done.
rewrite !nu_has in H2. done.
Qed.

Lemma Contains_contains : forall l l', ContainsInd l l' <-> contains (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i). 
Proof.
intros. split. apply/equiv_rInd2. move/containsP/Contains_co_ind=>//.
Qed.

Lemma containsb_complete : forall l0 l1, ContainsInd l0 l1 ->  containsb_wrap l0 l1.
Proof.
intros. apply:containsb_complete_aux. rewrite /uniq_pair. ssa. 
apply/Contains_contains.
intro. rewrite !Match_big_undup. move: s. apply/Contains_contains=>//.
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

(*Lemma c_eq_undup2 : forall l L, \big[Plus/Empt]_(i <- l) i  <⟨L⟩=  \big[Plus/Empt]_(i <- (undup l)) i.  
Proof.
elim;ssa.
case_if.  rewrite H. rewrite !big_cons. clear H.
elim: l a H0;ssa. 
rewrite !inE in H0. de (orP H0). norm_eqs. rewrite !big_cons. 
apply:c2_trans. 2: { apply:c2_trans.  2: { apply:c2_plus_assoc. }  apply:c2_plus_ctx. apply:c2_sym. apply:c2_plus_idemp. apply:c2_refl. } 
apply:c2_plus_ctx. done. done. rewrite !big_cons.
rewrite -c2_plus_assoc.
rewrite [a0 _+_ a] c2_plus_comm.
rewrite c2_plus_assoc. rewrite -(H a0) //. 
rewrite !big_cons.
apply:c2_plus_ctx. done. done.
Qed.*)

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
Proof. Admitted.

Lemma dsl_mon : forall T0 T1 r0 r1, dsl T0 r0 r1 -> (forall p v, PTree.get p T0 = Some v -> PTree.get p T1 = Some v) -> dsl T1 r0 r1.
Proof.
move=> T0 T1 r0 r1 d.
elim: d T1;auto.
intros. apply:ctrans. apply X. eauto. apply X0. eauto.
intros. apply:dsl_var. eauto.
intros.
have: forall (p : positive), PTree.get p T1 = None -> PTree.get p R = None.
intros. destruct (PTree.get p R) eqn:Heqn. apply H in Heqn. rewrite Heqn in H0. done. done.
move=>Hnone.
apply:dsl_fix. apply:Hnone.


Lemma decomp_p1 : forall l L,  \big[Plus/Empt]_(i <- l) i <⟨L⟩= (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof. 
intros.  
lct1. 
Check derive_unfold_coerce_l.
apply:derive_unfold_coerce_r.
rewrite (derive_unfold2 L (\big[Plus/Empt]_(i <- l) i)). 
apply:c2_plus_ctx.
rewrite /o_l.
destruct (has nu _) eqn:Heqn.
elim: l Heqn. rewrite big_nil //=.
ssa. rewrite big_cons /= /o /=.
destruct (nu _) eqn:Heqn2.  ssa. ssa. 
elim: l Heqn;ssa. rewrite big_nil //=. 
rewrite big_cons //=. rewrite /o //=. 
move/negP/negP: Heqn. rewrite negb_or. ssa.
rewrite (negbTE H0) /=.
have: has nu l = false. apply/negP/negP=>//. 
move/H. rewrite /o. done.
move: (index_enum A)=> l2.
elim: l2 l. intros.  rewrite !big_nil //=. 
ssa. rewrite !big_cons. 
apply:c2_plus_ctx.
apply:c2_seq_ctx. done.
rewrite big_derive. rewrite /pd_l.
rewrite c_eq_undup. 
clear H.
elim: l0. rewrite !big_nil. ssa.
ssa. rewrite !big_cons. rewrite c_eq_cat.
apply:c2_plus_ctx;ssa. clear H.
rewrite c_eq_derive_pd_l //. done.
Qed.

Lemma decomp_p2 : forall l L,  (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨L⟩=.  \big[Plus/Empt]_(i <- l) i 
