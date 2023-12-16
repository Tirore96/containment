From mathcomp Require Import all_ssreflect zify.
Require Import Paco.paco.
From Containment Require Import tactics utils regex enum modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module ExtensionalPartial (M : PredL).
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

Fixpoint bisim_complete_aux p l_v (H : D_bisim l_v p) {struct H} :  Extensional p.1 p.2 ->  reachable Pb H.  
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

Lemma bisim_complete : forall l0 l1, Extensional l0 l1 ->  reachable_wrap l0 l1 Pb.
Proof. intros. apply:bisim_complete_aux. apply/Extensional_equiv. 
intro. apply -> P_undup. move: s. apply/Extensional_equiv=>//.
Qed.

Fixpoint bisim_sound_aux p l_v (H : D_bisim l_v p) (R : @pder A -> @pder A -> Prop) {struct H} : 
(forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   reachable Pb H -> upaco2 exten_gen R p.1 p.2. 
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

Lemma bisim_sound : forall e0 e1, reachable_wrap e0 e1 Pb -> Extensional e0 e1.  
Proof. move => e0 e1 H. rewrite /reachable_wrap in H. 
apply:Bisim_co_ind=>s. apply/P_undup. move: s. apply/Extensional_equiv.
apply (@bisim_sound_aux _ _ _ bot2) in H. ssa. inv H. ssa.
Qed.

Lemma P_decidable : forall l0 l1, reachable_wrap l0 l1 Pb <-> (forall s, P s l0 l1).
Proof. intros. split. move/bisim_sound. move/Extensional_equiv.
move=> H s. eauto. intros. apply/bisim_complete. apply/Bisim_co_ind. done.
Qed.
End ExtensionalPartial.
