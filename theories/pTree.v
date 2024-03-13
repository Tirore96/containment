From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Coq.btauto.Btauto.
Require Import ConstructiveEpsilon.
From Containment Require Import  utils tactics regex modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section PTree.
Variable (A : eqType).
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

Fixpoint pflatten {r : regex} (T : pTree r) : seq A := 
match T with 
| p_tt => nil 
| p_singl a => (a :: nil )
| p_inl _ _ T' => pflatten T'
| p_inr _ _ T' => pflatten T'
| p_pair _ _ T0 T1 => (pflatten T0) ++ (pflatten T1)
| p_fold _ T' => pflatten T' 
end.

Lemma exists_pTree : forall (r : @regex A) s, Match s r -> exists (T : pTree r),(pflatten T == s).
Proof.
move => r s. elim=>//;eauto.
- exists p_tt. done.
- move=> x. exists (p_singl x). ssa. 
- move=> s1 c1 s2 c2 HM [] x Hf HM2 [] x' Hf2. 
  exists (p_pair x x')=>/=. ssa.   rewrite (eqP Hf) (eqP Hf2) //.
- move=> s1 c1 c2 HM [] x Hf. exists (p_inl x). done.
- move=> s1 c1 c2 HM [] x Hf. exists (p_inr x). done.
- move => c. exists (p_fold (p_inl p_tt)). done.
- move=> c s1 s2 HM [] x Hf HM2 [] x' Hf'. exists (p_fold (p_inr (p_pair x x')))=>/=. 
  ssa. rewrite (eqP Hf) (eqP Hf') //.
Qed.

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
Defined.

End PTree.
Arguments p_inl {A r0 r1}.
Arguments p_inr {A r0 r1}.
Arguments p_pair {A r0 r1}.
Arguments p_fold {A r}.
Arguments p_tt {A}.
Arguments p_singl {A}.
Ltac dep_destruct p :=
  pattern p; apply pTree_case; clear p; intros;try discriminate.


Hint Constructors pTree : pTree.

Lemma regex_dec : forall {A : eqType} (x y : @regex A), { x = y} + { x <> y }.
Proof. 
intros. de (eqVneq x y)=>//. constructor 2. apply/eqP=>//.
Qed.
Definition eq_regex  {A : eqType} (r0 : @regex A) := @Eqdep_dec.eq_rect_eq_dec _ regex_dec r0 pTree.
Ltac inv_eq := match goal with 
                   | [H : _ = _ |- _] => inv H
                 end.
Ltac clear_eq := match goal with 
                   | [H : ?x = ?x |- _] => clear H
                 end.


Ltac dp T f := move: T f;apply:pTree_case=>//; intros; inv_eq; move:f; rewrite <- eq_regex;clear_eq=>f. 
Ltac dp2 T f f' := move: T f f';apply:pTree_case=>//; intros; inv_eq; move:f f'; rewrite <- eq_regex;clear_eq=>f f'. 








Section UPTree.
Variable (A : eqType).

Inductive upTree : Type := 
| up_tt : upTree
| up_bot : upTree
| up_singl (a : A) : upTree
| up_inl : upTree -> upTree
| up_inr  : upTree -> upTree
| up_pair  : upTree -> upTree -> upTree
| up_fold : upTree  -> upTree.


Fixpoint uflatten (T : upTree) : seq A := 
match T with 
| up_tt => nil 
| up_singl a => (a :: nil )
| up_bot => nil
| up_inl T' => uflatten T'
| up_inr T' => uflatten T'
| up_pair T0 T1 => (uflatten T0) ++ (uflatten T1)
| up_fold T' => uflatten T' 
end.

Definition upTree_indDef := [indDef for upTree_rect].
Canonical upTree_indType := IndType upTree upTree_indDef.

Definition upTree_hasDecEq := [derive hasDecEq for upTree].
HB.instance Definition _ := upTree_hasDecEq.


(*Define extrinsically typed parse trees that are easier to write a generator for*)
Inductive typing : upTree -> regex  -> Type := 
| pt_tt : typing up_tt Eps 
| pt_singl a : typing (up_singl a) (Event a)
| pt_inl  r0 r1 p : typing p r0 -> typing (up_inl p) (r0 _+_ r1)
| pt_inr r0 r1 p : typing p r1 -> typing (up_inr p) (r0 _+_ r1)
| pt_pair r0 r1 p0 p1  : typing p0 r0 -> typing p1 r1 -> typing (up_pair p0 p1) (r0 _;_ r1)
| pt_fold r p : typing p (Eps _+_ (r _;_ (Star r))) -> typing (up_fold p) (Star r).
Hint Constructors typing.

Arguments pt_inl {r0 r1 p}.
Arguments pt_inr {r0 r1 p}.
Arguments pt_pair {r0 r1 p0 p1}.
Arguments pt_fold {r p}.



Fixpoint to_upTree {r : regex} (p : pTree r) : upTree := 
match p with 
| p_tt => up_tt
| p_singl a => up_singl a 
| p_inl _ _ p => up_inl (to_upTree p) 
| p_inr _ _ p => up_inr (to_upTree p)
| p_pair _ _ p0 p1 => up_pair (to_upTree p0) (to_upTree p1)
| p_fold _ p' => up_fold (to_upTree p')
end.




Lemma uflatten_to_upTree : forall r (x : pTree r),  uflatten (to_upTree x) = pflatten x.
Proof.
move=> r. elim=>//=.
move=> r0 r1 p Hf p0 Hf1. rewrite Hf Hf1 //.
Qed.



Hint Constructors Match.
Lemma pTree_Match : forall r T, typing T r -> Match (uflatten T) r.  
Proof.
move => r T. elim;ssa. inv H. inv H2. inv H2.  con. done. done.
Qed.


Lemma to_typing : forall r (x : pTree r), typing (to_upTree x) r.
Proof.
move=> r. elim=>//=;eauto.
Qed.



End UPTree.
Hint Constructors typing.
Arguments pt_inl {A r0 r1 p}.
Arguments pt_inr {A r0 r1 p}.
Arguments pt_pair {A r0 r1 p0 p1}.
Arguments pt_fold {A r p}.
Arguments pt_tt {A}.
Arguments pt_singl {A}.

Arguments up_tt {A}.
Arguments up_bot {A}.
Arguments up_singl {A}.
Arguments up_inl {A}.
Arguments up_inr  {A}.
Arguments up_pair  {A}.
Arguments up_fold {A}.
