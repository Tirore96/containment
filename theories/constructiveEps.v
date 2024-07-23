From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
Require Import ConstructiveEpsilon.
From Containment Require Import  utils tactics regex pTree. (* modules.*)
Set Implicit Arguments.
Set Maximal Implicit Insertion.


Section CoercionByConstructiveEpsilon.
Variable (A : finType).



(*Fixpoint upTree_0size p := 
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
Defined.*)





Arguments upTree { A}.


Fixpoint typingb (p : @upTree A) (r : regex) := 
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
Defined.

Lemma typingP2 : forall p r, typing p r -> typingb p r.
Proof.
move => p r. elim=>//.
- move=> a. simpl. done.
- intros. simpl. ssa.
Qed.



Fixpoint to_pTree {p : @upTree A} {r : regex} (H : typing p r) : pTree r := 
match H in typing p r return pTree r  with 
| pt_tt => p_tt
| pt_singl a => p_singl a 
| pt_inl _ _ _ p => p_inl (to_pTree p) 
| pt_inr _ _ _ p => p_inr (to_pTree p)
| pt_pair _ _ _ _ p0 p1 => p_pair (to_pTree p0) (to_pTree p1)
| pt_fold _ _ p' => p_fold (to_pTree p')
end.







Lemma pflatten_to_pTree : forall r (x : upTree) (H: typing x r), pflatten (to_pTree H) = uflatten x.
Proof.
move=> r x. elim=>//=;eauto;intros.
rewrite H H0. done.
Qed.



Definition genF (l : seq (@upTree A)) :=
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










Lemma has_sig : forall (A' : eqType) (f : A' -> bool) (l :seq A'), has f l -> { a | f a}.
Proof.
move => A' f. elim=>//.
move=> a l H. rewrite /=. destruct (f a) eqn:Heqn. move=>_.  econ. eauto.
simpl. eauto.
Defined.



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

Lemma Match_upTree : forall r s, Match s r -> { T : upTree | ((typingb T r): bool) /\ (uflatten T == s)}.
Proof.
move => r s HM.
move: (Match_sig_n  HM)=>[]n. move/has_sig=>[] x.
case Hcase: (typingb _ _)=>//=.
move/typingP1 : Hcase=>Ht.
move/eqP=>Hu. exists x. con. apply/typingP2=>//. apply/eqP. done.
Qed.

Lemma Match_pTree : forall (r : @regex A) s, Match s r -> { T : pTree r | (pflatten T == s)}.
Proof.
move => r s HM.
move: (Match_upTree HM).  
case=> x [] Ht /eqP Hf. 
exists (to_pTree (typingP1 _ _ Ht)). rewrite pflatten_to_pTree. apply/eqP=>//.
Qed.


(*Definition split_l {A : Type} (l : seq A) := map (fun n => (take n l,seq.drop n l)) (iota 0 (size l)).*)

Fixpoint split_l {A : Type} (l : seq A) := 
(nil,l)::
match l with 
| nil => nil
| a::l' => map (fun x => (a::(fst x),snd x)) (split_l l')
end.

Eval vm_compute in (split_l (0 :: 1 :: 2 ::3::nil)).



(*Fixpoint split_l {A : Type} (l l' : seq A) := 
(l,l')::
match l' with 
| nil => nil 
| a::l'' => split_l (l++[::a]) l''
end.*)

(*Lemma in_split_aux : forall (A : eqType) (l l' l0 l1: seq A), l0 ++ l1 = l ++ l' -> (l0,l1) \in split_l l l'.
Proof. Admitted.

Lemma in_split : forall (A : eqType) (l l0 l1: seq A), l0 ++ l1 = l -> (l0,l1) \in split_l nil l.
Proof. Admitted.*)

Lemma in_split : forall (A : eqType) (s1 s2 : seq A), (s1, s2) \in split_l (s1 ++ s2).
Proof.
move=> A0. elim. ssa. de s2.
move=> a l IH. ssa. rewrite inE.  apply/orP. right. apply/mapP. econ. eauto. done.
Qed.

Lemma pTree_nu : forall (r : @regex A), nu r = true -> {T : pTree r | pflatten T = nil}.
Proof.
elim;ssa. exists p_tt. done. 
destruct (nu r) eqn:Heqn. 
de X. exists (p_inl x). done.
ssa. de X0. exists (p_inr x). done.
apply X in H0. apply X0 in H1. de H0. de H1.
exists (p_pair x x0). ssa. rewrite e e0. done.
exists (p_fold (p_inl (p_tt))). done.
Qed.



Lemma pTree_der : forall (r : @regex A) a (T : pTree (derive a r)), {T' : pTree r | pflatten T' = a::(pflatten T) }.
Proof.
elim.
move=> a. simpl. ssa. inv T. ssa. inv T.
move=> s a.
ssa.  move : T. de (eqVneq s a). subst. 
exists (p_singl a). ssa. 
move : T. apply:pTree_case=>//;intros;inv_eq. rewrite -eq_regex //.  
inv T.
ssa. 
move : T. apply:pTree_case=>//;intros;inv_eq. rewrite -eq_regex //=.  
move: (@X a p).
case. ssa. exists (p_inl x). done.
move: (@X0 a p).
case. ssa. rewrite -eq_regex //=. exists (p_inr x). done.

ssa. 
move : T. 
destruct (nu r) eqn:Heqn.
apply:pTree_case=>//;intros;inv_eq. rewrite -eq_regex //.  simpl.
move : p. apply:pTree_case=>//;intros;inv_eq. rewrite -eq_regex //=.  

move: (X a p0). case. ssa. exists (p_pair x p1). ssa. rewrite p. done.
move: (X0 a p). case.
ssa. apply pTree_nu in Heqn. de Heqn.
exists (p_pair x0 x). ssa. rewrite -eq_regex. ssa. rewrite e p0. done.


apply:pTree_case=>//;intros;inv_eq. rewrite -eq_regex //.  simpl.
move: (X a p0). case. ssa. exists (p_pair x p1). ssa. rewrite p. done.
ssa.

move : T. 
apply:pTree_case=>//;intros;inv_eq. rewrite -eq_regex //.  simpl.
move: (X a p0). case. ssa. exists ((p_fold (p_inr (p_pair x p1)))). ssa. rewrite p. done.
Qed.

Lemma pTree_maybe : forall s (r : @regex A), sumor ({T : pTree r | pflatten T == s}) (~ Match s r).
Proof.
elim;ssa.
destruct (nu r) eqn:Heqn.
apply pTree_nu in Heqn. de Heqn. left. exists x. apply/eqP. done.
right. intro. move/nuP : H. rewrite Heqn. done.
de (X (a \ r)). de s. 
move: (@pTree_der _ _ x).
case. ssa. left. exists x0. apply/eqP. rewrite (eqP i) in p. done.
right. intro. apply : n.
move/deriveP : H. done.
Defined.

Definition parse_string : forall s (r : @regex A), Match s r -> {T : pTree r | pflatten T == s}.
Proof.
intros. move: (pTree_maybe s r). case. done. done.
Defined.

Example test : 0 == 0.
Unset Printing Notations.
rewrite /eq_op. Definition nr := @regex nat. Print Equality.axioms_. 
 Check (nr : Prop).
 Check (Datatypes_nat__canonical__eqtype_Equality : Set). eqType.
 Check ( hasDecEq.eq_op (Equality.class Datatypes_nat__canonical__eqtype_Equality)).

  
(*suff: {TT : (pTree r * pTree r0) | pflatten (p_pair (fst TT) (snd TT)) == s} + {~ exists s0 s1, (s0,s1) \in split_l s /\ Match s0 r /\ Match s1 r0}.
  ssa. de X1. de s0. left. exists (p_pair (fst x) (snd x)). ssa.
  right. intro. apply n. inv H. econ. econ. con. 2:con;eauto. apply in_split.
  move Heq: (split_l s) => l.
  elim : l s Heq.
  ssa. right. intro. ssa.
  ssa. de s. inv Heq.*)
  de (X nil). de s.
  de (X0 nil). de s. left. exists (p_pair x x0). ssa. rewrite (eqP i) (eqP i0). done.
  right. intro. inv H. de s1. subst. done.
  right. intro. inv H. de s1. 
  ssa.
ssa. rewrite inE in H. norm_eqs. inv H.
  right. intro. ssa. rewrite inE in H. norm_eqs. inv H.
  inv Heq. clear Heq.
  edestruct X1. simpl.
  left. exists (p_tt,p_tt).
  

 have : s = nil ++ s. done. move=>->.
  


suff: 
 {T : pTree (r _;_ r0) | pflatten T == s} + {~ Match s (r _;_ r0)}
right. intro. inv H.

move Heq: (split_l s) => l.
  elim : l s Heq.
  de s.
  de (X nil). de s.
  de (X0 nil). de s. left. exists (p_pair x x0). ssa. rewrite (eqP i) (eqP i0). done.
  right. intro. inv H. de s1. subst. done.
  right. intro. inv H. de s1.
  ssa.
  de X1.
- de s. left. Print pTree. exists (p_fold (p_inl p_tt)). done.
  right. intro. inv H.


Definition constr_eps_coerce r0 r1 (H : contains_r r0 r1): pTree r0 -> pTree r1 := 
fun T =>  (proj1_sig (Match_pTree (H _ (pTree_Match (to_typing T))))).

Lemma constr_eps_coerce_pres_string : forall r0 r1 (H : contains_r r0 r1) (T : pTree r0), pflatten (constr_eps_coerce  H T) = pflatten T. 
Proof.
intros. rewrite /constr_eps_coerce /=. 
destruct ((Match_pTree (H (uflatten (to_upTree T)) (pTree_Match (to_typing T))))) eqn:Heqn.
simpl. rewrite (eqP i). rewrite uflatten_to_upTree //.
Qed.

End CoercionByConstructiveEpsilon.
