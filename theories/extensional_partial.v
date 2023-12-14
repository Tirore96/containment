Require Import Program. 
From Equations Require Import Equations.  
From mathcomp Require Import all_ssreflect zify.
Require Import Paco.paco.
From Containment Require Import tactics utils regex enum modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.


Module ExtensionalPartial (M : Pred).
Import M.

Inductive exten_gen bisim : pder -> pder-> Prop :=
 contains_con2 l0 l1 (H0: forall e, bisim (pd_l e l0) (pd_l e l1) : Prop ) (H1: Pb l0 l1 (*has nu l0 = has nu l1*)) : exten_gen bisim l0 l1.

Definition Extensional l0 l1 := paco2 exten_gen bot2 l0 l1.
Hint Unfold  Extensional : core.

Lemma exten_gen_mon: monotone2 exten_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve exten_gen_mon : paco.


Theorem equiv_rInd : forall l l', Extensional l l' -> forall s, P s l l'.  
Proof.
move=> l0 l1 HC s. 
elim: s l0 l1  HC.
- move=> c0 c1. intros. punfold HC. case: HC. move=> ce c3 HC HC'.
  apply Pb_P_iff. done.
- move=> a l IH c0 c1. move=>HC.  punfold HC. case: HC. intros.
  case: (H0 a)=>//. intros.
(*elim.
  move=> c2 c3 /(_ a) [] // HC _. *)
  apply/P_derive. apply IH. done.
Qed.

Theorem Bisim_co_ind : forall l l', (forall s, P s l l') -> Extensional l l'.
Proof.
pcofix CIH. move=> l l'. pfold. con. 
intros. right. apply:CIH. intros.
apply P_derive. apply H0.
apply/Pb_P_iff. done.
Qed.

Lemma Extensional_equiv : forall l l', Extensional l l' <->  forall s, P s l l'. 
Proof.
intros. split. apply/equiv_rInd. apply:Bisim_co_ind.
Qed.



















(*Definition undup2 (pp : @nType A) := (undup pp.1,undup pp.2).

Lemma pair_uniq_proof : forall pp, uniq_pair (undup2 pp). 
Proof.
intros. rewrite /uniq_pair. ssa; apply/undup_uniq.
Qed.

Definition bisim (p : @pType A) (H : uniq_pair p.2) : bool.
move: p H.
Check measure_rect.
apply: (@measure_rect A).
intros. destruct (p.2 \in p.1) eqn:Heqn. 
- apply true.
- have: p.2 \notin p.1. lia. move=> Hnot.
  move: (myRel_lt p.1 p.2 H Hnot). move=>HH.
  have : (forall (a : A), bool).
  move=> a. move: (HH a). move/X. simpl. 
  have: (uniq_pair (pair_pd_l a p.2)). 
  rewrite /pair_pd_l /pd_l. rewrite /uniq_pair. ssa; apply undup_uniq.
  move=>Hun. move/(_ Hun). move=> B. apply B.
  move=> f. apply (all f (index_enum A)).
Defined.


Extraction Inline measure_rect.
Extraction bisim.




  move/(_ (pair_uniq_proof _)).
rewrite /uniq_pair.
  
  have : (forall a, 
clear X Heqn Hnot H.
  move: (index_enum A) => l.
  elim: p. intros. simpl in measure_lt.
  move=>HH. 
  have: (forall (a : A), 
 move: X. clear Heqn.
admit.
apply A.
Hint Resolve undup_uniq.
Unset Implicit Arguments.
Implicit Type (pp : (@pder A) * (@pder A)).
Implicit Type (visited : seq ((@pder A) * (@pder A))).
(*Less effecient*)
Equations bisim pp visited : bool by wf (r_measure visited pp) := 
 bisim pp visited  with (dec (pp \in visited)) => {
  bisim _  _ (in_left) := true;
  bisim pp visited (in_right) with (dec (uniq_pair pp)) => { 
        bisim pp visited _ (in_left) := (Pb pp.1 pp.2) && 
                                        (foldInAll (index_enum A) (fun e _ => bisim (pair_pd_l e (pp)) (pp::visited)));
        bisim pp visited _ (in_right) := false }
 }.
Next Obligation.
intros.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.

(*Effecient but awkard for proofs*)
Equations bisim2 pp visited (H : uniq_pair pp) : bool by wf (r_measure visited pp) := 
 bisim2 pp visited H  with (dec (pp \in visited)) => {
  bisim2 _  _ _ (in_left) := true;
  bisim2 pp visited _ (in_right) := (Pb pp.1 pp.2) && 
                                           (foldInAll (index_enum A) (fun e _ => bisim2 (pair_pd_l e pp) (pp::visited) _));
 }.
Next Obligation. 
intros. apply/andP.
con. simpl. rewrite /pd_l. done.  simpl. rewrite /pd_l. done.
Defined.
Next Obligation.
intros. apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.
Set Implicit Arguments.

Lemma bisim12 : forall pp visited (H : uniq_pair pp), bisim pp visited -> bisim2 pp visited H.
Proof.
intros. funelim (bisim pp visited).
simp bisim2. simpl. rewrite Heq. simpl. done.
simp bisim2. rewrite Heq0. simpl.
rewrite -Heqcall in H1. ssa.
rewrite !foldInAllP in H3 *. 
apply/allP. intro. intros. move: (allP H3 _ H1). move/H. move/inP: H1=>H1'. move/(_ H1')=>Hall.
apply Hall. rewrite -Heqcall in H0. done.
Qed.

Lemma bisim21 : forall pp visited (H : uniq_pair pp), bisim2 pp visited H -> bisim pp visited.
Proof.
intros. funelim (bisim pp visited). rewrite -Heqcall. done.
rewrite -Heqcall. simp bisim2 in H1. rewrite Heq0 in H1. ssa.
rewrite !foldInAllP in H3 *. 
apply/allP. intro. intros. move: (allP H3 _ H1). move/H. move/inP: H1=>H1'. move/(_ H1')=>Hall.
apply Hall.  clear H0.
rewrite e1 in H. done.
Qed.

Lemma bisim_iff : forall pp visited (H : uniq_pair pp), bisim pp visited <-> bisim2 pp visited H.
Proof.
intros. split. apply:bisim12. apply:bisim21.
Qed.*)
Fixpoint bisim_complete_aux p l_v (H : D_bisim l_v p) {struct H} :  Extensional p.1 p.2 ->  reachable Pb H.  
refine( 
match H with 
| Db_stop x y z => _ 
| _ => _ 
end).
- 
simpl in x,y,z. intros.
have:  exten_gen (upaco2 exten_gen bot2) y.1 y.2. clear bisim_complete_aux. punfold H0.
clear H0. move=> He.  move: He z. case.
intros. simpl. destruct (dec _). done.
exfalso. rewrite z in e. done.
simpl in p0. intros.
have:  exten_gen (upaco2 exten_gen bot2) p1.1 p1.2.
punfold H0.
clear H0=>H0. destruct p1. simpl in *.
destruct (dec _). done.
move: H0 i i0 d. clear e.
case. intros. ssa. 
apply/allP. intro. intros.
apply (bisim_complete_aux _ _ (d x)). simpl.
clear bisim_complete_aux. simpl. case: (H0 x). ssa. done.
Qed.

Lemma bisim_complete : forall l0 l1, Extensional l0 l1 ->  reachable_wrap l0 l1 Pb.
Proof.
intros. apply:bisim_complete_aux. 
apply/Extensional_equiv. 
intro.
apply -> P_undup. move: s.
apply/Extensional_equiv=>//.
Qed.

Fixpoint bisim_sound_aux p l_v (H : D_bisim l_v p) (R : @pder A -> @pder A -> Prop) {struct H} : (forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   reachable Pb H -> upaco2 exten_gen R p.1 p.2. 
refine( 
match H with 
| Db_stop x y z => _ 
| _ => _ 
end).
ssa.
- right.  apply/H0. destruct y. ssa. 
- simpl. intros. left. destruct (dec _). rewrite e in i. done.
  destruct (andP H1).
  pcofix CIH. pfold. con. intros. 
  eapply (bisim_sound_aux (pd_l e0 p1.1,pd_l e0 p1.2)).  
  simpl. 2: { apply (allP H3). done. } 
  intros. rewrite !inE in H4. destruct (orP H4). 
  norm_eqs. ssa.  eauto. done.
Qed.

Lemma bisim_sound : forall e0 e1, reachable_wrap e0 e1 Pb -> Extensional e0 e1.  
Proof. move => e0 e1 H. 
rewrite /reachable_wrap in H. 
apply:Bisim_co_ind=>s. apply/P_undup.
move: s. apply/Extensional_equiv.
apply (@bisim_sound_aux _ _ _ bot2) in H. ssa. inv H. 
ssa.
Qed.

Lemma P_decidable : forall l0 l1, reachable_wrap l0 l1 Pb <-> (forall s, P s l0 l1).
Proof.
intros. split. move/bisim_sound. move/Extensional_equiv.
move=> H s. eauto.
intros. apply/bisim_complete. apply/Bisim_co_ind. done.
Qed.

(*Proof. 
move=> p V. elim;ssa.
intros. funelim (bisim  (l0,l1) l_v).  rewrite -Heqcall. ssa.
rewrite -Heqcall. ssa. 
punfold H1.  inv H1. 
rewrite foldInAllP. apply/allP=> x xIn. 
apply:H. apply/inP. eauto.  simpl. 
rewrite /uniq_pair /pd_l. ssa.
punfold H1. inv H1. case: (H2 x)=>//. con. 
done. rewrite  e1 in H. done.
Qed.
Fixpoint reachable (V : vType) (p : nType) (H : D_bisim V p) {struct H} : bool.


Lemma bisim_complete_aux : forall l0 l1 l_v, uniq_pair (l0,l1) ->  Extensional l0 l1 ->  bisim  (l0,l1) l_v.  
Proof. 
intros. funelim (bisim  (l0,l1) l_v).  rewrite -Heqcall. ssa.
rewrite -Heqcall. ssa. 
punfold H1.  inv H1. 
rewrite foldInAllP. apply/allP=> x xIn. 
apply:H. apply/inP. eauto.  simpl. 
rewrite /uniq_pair /pd_l. ssa.
punfold H1. inv H1. case: (H2 x)=>//. con. 
done. rewrite  e1 in H. done.
Qed.

Lemma bisim_complete_aux2 : forall l0 l1 l_v (H : uniq_pair (l0,l1)),  Extensional l0 l1 ->  bisim2  (l0,l1) l_v H.  
Proof.
intros. apply/bisim_iff. apply:bisim_complete_aux. done. done.
Qed.



Definition bisim_wrap l l' := bisim2 (undup l,undup l') nil (pair_uniq_proof (l,l')).
*)




End ExtensionalPartial.
