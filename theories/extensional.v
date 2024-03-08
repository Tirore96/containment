Require Import Program. 
From mathcomp Require Import all_ssreflect zify.
Require Import Paco.paco.

From Containment Require Import tactics utils regex enum pred.
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
Qed.

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


Definition undup2 pp := (undup pp.1,undup pp.2).
Lemma pair_uniq_proof : forall pp, uniq_pair (undup2 pp). 
Proof.
intros. rewrite /uniq_pair. ssa.
Qed.
Definition bisim_wrap l l' := bisim2 (undup l,undup l') nil (pair_uniq_proof (l,l')).

Lemma bisim_complete : forall l0 l1, Extensional l0 l1 ->  bisim_wrap l0 l1.
Proof.
intros. apply:bisim_complete_aux2. 
apply/Extensional_equiv. 
intro.
apply -> P_undup. move: s.
apply/Extensional_equiv=>//.
Qed.

Lemma bisim_sound_aux : forall e0 e1 l_v (R : @pder A -> @pder A -> Prop), (forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   bisim (e0,e1) l_v -> upaco2 exten_gen R e0 e1. 
Proof. 
move => e0 e1 /= l_v R.  intros. funelim (bisim (e0,e1) l_v).
right.  apply/H=>//=.
left. pcofix CIH. pfold. rewrite -Heqcall in H1.
destruct (andP H1).  ssa.
rewrite foldInAllP in H3. con. 
intros. eapply H. 3: {  apply (allP H3). done. } 3: { con. }  apply/inP. done. 
intros. rewrite !inE in H1. de (orP H1). norm_eqs. inv H6. done. eauto.
rewrite -Heqcall in H0. done.
Qed.

Lemma bisim_sound : forall e0 e1, bisim_wrap e0 e1 -> Extensional e0 e1.  
Proof. move => e0 e1 H. 
rewrite /bisim_wrap in H. apply bisim_iff in H. apply:Bisim_co_ind=>s. apply/P_undup.
move: s. apply/Extensional_equiv.
suff: upaco2 exten_gen bot2 (undup e0) (undup e1). case=>//=. 
apply/bisim_sound_aux.  2:eauto. done.
Qed.

Lemma P_decidable : forall l0 l1, bisim_wrap l0 l1 <-> (forall s, P s l0 l1).
Proof.
intros. split. move/bisim_sound. move/Extensional_equiv.
move=> H s. eauto.
intros. apply/bisim_complete. apply/Bisim_co_ind. done.
Qed.
End ExtensionalPartial.
