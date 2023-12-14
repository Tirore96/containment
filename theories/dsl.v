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
From Coq.Logic Require Import Eqdep_dec.
From Containment Require Import  tactics utils regex pred modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.



Let inE := tactics.inE.
Module MyPredF2 (M : FModule) <: Pred.
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
End MyPredF2.

(*Module Type ContainerM.
Parameter (F : Type -> Type).
End ContainerM.*)

Module MyDSL (M : FModule).
Import M.
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


Require Import MSets.MSetRBT.
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
Inductive pTree : @regex A -> Type := 
| p_tt : pTree Eps 
| p_singl a : pTree (Event a)
| p_inl r0 r1 : pTree r0 -> pTree (r0 _+_ r1) 
| p_inr r0 r1 : pTree r1 -> pTree (r0 _+_ r1) 
| p_pair r0 r1 : pTree r0 -> pTree r1 -> pTree (r0 _;_ r1)
| p_fold r : pTree (Eps _+_ (r _;_ (Star r))) -> pTree (Star r).
Hint Constructors pTree : pauto.
Arguments p_inl {r0 r1}.
Arguments p_inr {r0 r1}.
Arguments p_pair {r0 r1}.
Arguments p_fold {r}.


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



Fixpoint pflatten {r : regex} (T : pTree r) : seq A := 
match T with 
| p_tt => nil 
| p_singl a => (a :: nil )
| p_inl _ _ T' => pflatten T'
| p_inr _ _ T' => pflatten T'
| p_pair _ _ T0 T1 => (pflatten T0) ++ (pflatten T1)
| p_fold _ T' => pflatten T' 
end.
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


Print pTree.
Check @eq_rect regex Eps pTree p_tt. 
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
have: (forall (n : positive) (x0 y : regex),
    PTree.get n tree = Some (x0, y) -> forall T0 : pTree x0, pRel0 T0 x -> post y T0).
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

End InductiveInterpretation.



