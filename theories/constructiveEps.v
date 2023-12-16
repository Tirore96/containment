From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
Require Import ConstructiveEpsilon.
From Containment Require Import  utils tactics regex modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Constructive (M : FModule).
Import M.
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

(*This section shows how a proof (H : forall s, Match s r -> Match s r' in the Prop world 
 can be "pulled down" to Types, giving us a coercion on parse trees.
 It is ineffecient, and serves as a comparison. 
 I.e, this is the base line, with no regard to effeciency
*)
Section CoercionByConstructiveEpsilon.

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


Fixpoint upTree_0size p := 
match p with 
| up_tt =>  1 
| up_bot => 1 
| up_singl _ => 1
| up_inl p0 => (upTree_0size p0).+1
| up_inr p0 => (upTree_0size p0).+1
| up_pair p0 p1=> ((upTree_0size p0) + (upTree_0size p1)).+1
| up_fold p0 => (upTree_0size p0).+1
end.


Lemma upTree_1size1 : forall p, 0 < upTree_0size p.
Proof.
elim=>//.
Qed.

Definition upRel (T0 T1 : upTree) := upTree_0size T0 < upTree_0size T1.

Lemma upTree_0size_rect
     : forall (P : upTree -> Type),
       (forall (u  : upTree ), (forall u' : upTree, upRel u' u -> P u') -> P u) ->
       forall (p : upTree ), P p.
Proof.
move=> P  Hsize u. 
have: Acc upRel u. clear Hsize. 
move Heq : (upTree_0size u)=>n. move: n Heq.
suff : forall n : nat, upTree_0size u <= n -> Acc (fun p' p : upTree => upRel p' p) u.
intros. eauto.
move=>n. elim: n u.
intros. con. intros. rewrite /upRel in H0. lia.
intros. con. intros. apply/H. rewrite /upRel in H1. lia.
move=>Hacc.
move: u Hacc Hsize. apply: Acc_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.




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


Fixpoint typingb (p : upTree) (r : regex) := 
match p with
| up_tt => r == Eps 
| up_bot => false 
| up_singl a => r == (Event a)
| up_inl p0 => if r is Plus r0 _ then typingb p0 r0 else false 
| up_inr p0 => if r is Plus _ r1 then typingb p0 r1 else false 
| up_pair p0 p1 => if r is Seq r0 r1 then (typingb p0 r0) && (typingb p1 r1) else false 
| up_fold p => if r is Star r0 then typingb p  (Eps _+_ (r0 _;_ (Star r0))) else false
end.

Lemma typingP1 : forall p r, typingb p r -> typing p r.
Proof.
elim=>//.
- case=>//. 
- move=>a.  case=>// s //=. move/eqP=>->. done.
- move=> u IH r /=. destruct r;ssa.
- move=> u IH r. destruct r;ssa.
- move=> u IH u0 IH2 r /=. destruct r;ssa.
- move=> u IH r /=. destruct r;ssa. 
Qed.

Lemma typingP2 : forall p r, typing p r -> typingb p r.
Proof.
move => p r. elim=>//.
- move=> a. simpl. done.
- intros. simpl. ssa.
Qed.


Fixpoint to_upTree {r : regex} (p : pTree r) : upTree := 
match p with 
| p_tt => up_tt
| p_singl a => up_singl a 
| p_inl _ _ p => up_inl (to_upTree p) 
| p_inr _ _ p => up_inr (to_upTree p)
| p_pair _ _ p0 p1 => up_pair (to_upTree p0) (to_upTree p1)
| p_fold _ p' => up_fold (to_upTree p')
end.

Fixpoint to_pTree {p : upTree} {r : regex} (H : typing p r) : pTree r := 
match H in typing p r return pTree r  with 
| pt_tt => p_tt
| pt_singl a => p_singl a 
| pt_inl _ _ _ p => p_inl (to_pTree p) 
| pt_inr _ _ _ p => p_inr (to_pTree p)
| pt_pair _ _ _ _ p0 p1 => p_pair (to_pTree p0) (to_pTree p1)
| pt_fold _ _ p' => p_fold (to_pTree p')
end.





Lemma uflatten_to_upTree : forall r (x : pTree r),  uflatten (to_upTree x) = pflatten x.
Proof.
move=> r. elim=>//=.
move=> r0 r1 p Hf p0 Hf1. rewrite Hf Hf1 //.
Qed.

Lemma pflatten_to_pTree : forall r (x : upTree) (H: typing x r), pflatten (to_pTree H) = uflatten x.
Proof.
move=> r x. elim=>//=;eauto;intros.
rewrite H H0. done.
Qed.



Definition genF (l : seq upTree) :=
  (up_tt::up_bot::(map up_singl (index_enum A)))++
  (map up_inl l)++
  (map up_inr l)++
  (map (fun p => up_pair p.1 p.2) (compose l l pair))++
  (map up_fold l).

Fixpoint gen_upTree (n : nat) := 
if n is n'.+1 then let l:=(gen_upTree n') in l++(genF l) else nil.

Lemma in_gen_upTree_plus : forall (i n : nat) T, T \in gen_upTree n -> T \in gen_upTree (i + n).
Proof.
elim=>//.
move=> n IH n0 T Hin /=. rewrite mem_cat IH //.
Qed.

Lemma in_gen_upTree_le : forall (n n' : nat) T, n <= n' -> T \in gen_upTree n -> T \in gen_upTree n'.
Proof.
intros.
have : exists n'', n' = n + n''. clear H0. elim:  n n' H=>//. move=> n'  _. exists n'.    done. 
move=> n IH n' Hl. destruct n'. done.
have : n <= n' by lia. move/IH. case. move=> x Hin. exists x. rewrite Hin //.  
case=> x Heq. subst. rewrite addnC. apply/in_gen_upTree_plus. done.
Qed.

Lemma in_gen_upTree : forall (T : upTree), exists n, T \in gen_upTree n.
Proof.
elim=>//.
- exists 1. rewrite /= /genF //= !inE.
- exists 1. rewrite /= /genF //= !inE.
- exists 1. rewrite /= /genF //= !inE. apply/orP. right. 
  apply/orP. right. 
  rewrite mem_cat. apply/orP. left.
  apply/map_f. apply/mem_index_enum.
- move=> u [] x Hin. exists x.+1. rewrite /= mem_cat /genF /= !inE.
  apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. right.
  apply/orP. left. apply/map_f. done.
- move=> u [] x Hin. exists x.+1. rewrite /= mem_cat /genF /= !inE.
  apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. right.
  apply/orP. right.  apply/orP. left. apply/map_f. done.
- move=> u [] x Hin u' [] x' Hin'. exists (x + x').+1.
  rewrite /= mem_cat /genF /=. rewrite !inE. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. right. apply/orP. right.
  apply/orP. right. apply/orP. right. apply/orP. left. 
  apply/mapP. econ.  apply/mem_compose. apply/in_gen_upTree_le. 
  2: {  apply/Hin. } lia. 
  apply/in_gen_upTree_le. 2 : { apply/Hin'. } lia. done.
- move=> u [] x Hin. exists x.+1. rewrite /= !mem_cat /genF /= !inE.
  apply/orP. right. apply/orP. right. apply/orP. right. apply/orP. right.
  apply/orP. right. apply/map_f. done.
Qed.





Lemma to_typing : forall r (x : pTree r), typing (to_upTree x) r.
Proof.
move=> r. elim=>//=;eauto.
Qed.






Lemma has_sig : forall (A' : eqType) (f : A' -> bool) (l :seq A'), has f l -> { a | f a}.
Proof.
move => A' f. elim=>//.
move=> a l H. rewrite /=. destruct (f a) eqn:Heqn. move=>_.  econ. eauto.
simpl. eauto.
Defined.

Lemma exists_pTree : forall r s, Match s r -> exists (T : pTree r),(pflatten T == s).
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

Lemma exists_upTree : forall r s, Match s r -> exists (T : upTree), (typingb T r) &&  (uflatten T == s).
Proof.
move => r s. elim=>//;eauto.
- exists up_tt. done.
- move=> x. exists (up_singl x). ssa. 
- move=> s1 c1 s2 c2 HM [] x Hf HM2 [] x' Hf2. 
  exists (up_pair x x')=>/=. ssa.   rewrite (eqP H0) (eqP H2) //.
- move=> s1 c1 c2 HM [] x Hf. exists (up_inl x). done.
- move=> s1 c1 c2 HM [] x Hf. exists (up_inr x). done.
- move => c. exists (up_fold (up_inl up_tt)). done.
- move=> c s1 s2 HM [] x Hf HM2 [] x' Hf'. exists (up_fold (up_inr (up_pair x x')))=>/=. 
  ssa. rewrite (eqP H0) (eqP H2) //.
Qed.


Lemma Match_exists_n : forall s r, Match s r -> exists n, has (fun x => (typingb x r) && (uflatten x == s)) (gen_upTree n).  
Proof.
move=> s r HM. case: (exists_upTree  HM)=> x Hf.
case:(in_gen_upTree x)=> x0 Hin. exists x0.
apply/hasP. exists x. done. apply/andP. con. ssa. ssa. 
Qed.

(*We use Constructive Epsilon library*)
Lemma Match_sig_n : forall s r, Match s r -> { n | has (fun x => (typingb x r) && (uflatten x == s)) (gen_upTree n)}.  
Proof.
move=> s r HM.
apply: constructive_indefinite_ground_description. instantiate (1 := id). instantiate (1:= id). done.
move=> x. case Hcase: (has _ _)=>//. con. done. right. done.
apply/Match_exists_n. done.
Qed.

Lemma Match_upTree : forall r s, Match s r -> { T : upTree | prod ((typingb T r): bool) (uflatten T == s)}.
Proof.
move => r s HM.
move: (Match_sig_n  HM)=>[]n. move/has_sig=>[] x.
case Hcase: (typingb _ _)=>//=.
move/typingP1 : Hcase=>Ht.
move/eqP=>Hu. exists x. con. apply/typingP2=>//. apply/eqP. done.
Qed.

Lemma Match_pTree : forall r s, Match s r -> { T : pTree r | (pflatten T == s)}.
Proof.
move => r s HM.
move: (Match_upTree HM).  
case=> x [] Ht /eqP Hf. 
exists (to_pTree (typingP1 _ _ Ht)). rewrite pflatten_to_pTree. apply/eqP=>//.
Qed.

Hint Constructors Match.
Lemma pTree_Match : forall r T, typing T r -> Match (uflatten T) r.  
Proof.
move => r T. elim;ssa. inv H. inv H2. inv H2.  con. done. done.
Qed.

Definition constr_eps_coerce r0 r1 (H : contains_r r0 r1): pTree r0 -> pTree r1 := 
fun T =>  (proj1_sig (Match_pTree (H _ (pTree_Match (to_typing T))))).

Lemma constr_eps_coerce_pres_string : forall r0 r1 (H : contains_r r0 r1) (T : pTree r0), pflatten (constr_eps_coerce  H T) = pflatten T. 
Proof.
intros. rewrite /constr_eps_coerce /=. 
destruct ((Match_pTree (H (uflatten (to_upTree T)) (pTree_Match (to_typing T))))) eqn:Heqn.
simpl. rewrite (eqP i). rewrite uflatten_to_upTree //.
Qed.

End CoercionByConstructiveEpsilon.

End Constructive.
