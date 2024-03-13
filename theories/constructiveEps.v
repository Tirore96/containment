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


Definition constr_eps_coerce r0 r1 (H : contains_r r0 r1): pTree r0 -> pTree r1 := 
fun T =>  (proj1_sig (Match_pTree (H _ (pTree_Match (to_typing T))))).

Lemma constr_eps_coerce_pres_string : forall r0 r1 (H : contains_r r0 r1) (T : pTree r0), pflatten (constr_eps_coerce  H T) = pflatten T. 
Proof.
intros. rewrite /constr_eps_coerce /=. 
destruct ((Match_pTree (H (uflatten (to_upTree T)) (pTree_Match (to_typing T))))) eqn:Heqn.
simpl. rewrite (eqP i). rewrite uflatten_to_upTree //.
Qed.

End CoercionByConstructiveEpsilon.
