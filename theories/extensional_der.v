

Inductive bisimilarity_gen bisim : @regex A -> regex -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: Pb [::c0] [::c1]) : bisimilarity_gen bisim c0 c1.

Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.

Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.

Hint Resolve bisimilarity_gen_mon : paco.

Axiom P_r_derive : forall r0 r1 e, (forall s, P s r0 r1) -> (forall s,P s (e \ r0) (e \ r1)).
Axiom P_r_trans : forall r0 r1 r2, (forall s, P s r0 r1) -> (forall s, P s r1 r2) -> (forall s, P s r0 r2).
Axiom P_r_sym : forall r0 r1, (forall s, P s r0 r1) -> (forall s,P s r1 r0). 




Theorem P_r1 : forall c0 c1, (forall s, P s c0 c1) -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  move=> s.  apply:P_r_derive. eauto.
  apply/Pb_P_iff.  rewrite !big_cons !big_nil.
  apply P_empt. done.
Qed.

(*Theorem equiv_r1 : forall c0 c1, equiv_r c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  rewrite /equiv_r. move=> s.  rewrite -!deriveP. eauto.
  move: (H0 nil). rewrite !matchbP /matchb /=. 
  move/eq_iff=>->//.
Qed.
*)
Theorem P_r2 : forall c0 c1, Bisimilarity c0 c1 -> (forall s, P s c0 c1). 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. apply Pb_P_iff in HC'.
  rewrite !big_cons !big_nil in HC'. apply P_empt. eauto.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. Search _ P.
rewrite !deriveP. apply/IH=>//.
Qed.
Theorem equiv_r2 : forall c0 c1, Bisimilarity c0 c1 -> equiv_r c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. rewrite !matchbP /matchb /= HC' //.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.


Theorem equivP : forall c0 c1, equiv_r c0 c1 <-> Bisimilarity c0 c1.
Proof.
move=> c0 c1. con. apply/equiv_r1. apply/equiv_r2.
Qed.

Lemma derive_pd_l : forall (l : @pder A) e, equiv_r (e \ \big[Plus/Empt]_(i <- l) i) 
                                   (\big[Plus/Empt]_(i <- pd_l e l) i).
Proof.
intros. intro.
rewrite der_eq /pd_sum.
rewrite -pd_plus.
rewrite Match_big_undup //. 
Qed.

Lemma has_nuP : forall (l : @pder A), has nu l <->  Match [::] (\big[Plus/Empt]_(i <- l) i).
Proof.
intros. split. apply/Match_has_nu. apply/has_nu_Match.
Qed.

Lemma has_nuP2 : forall (l : @pder A), has nu l = nu (\big[Plus/Empt]_(i <- l) i).
Proof.
intros. apply/eq_iff. split. move/has_nuP=>//.  rewrite matchbP. done.
intros. apply/has_nuP. apply/matchbP. done.
Qed.

Theorem Bisim_Ext : forall l l', Bisimilarity (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i) -> Extensional l l'.
Proof.
pcofix CIH. intros. punfold H0. inv H0. pfold. con. intros.
right. apply/CIH. 
destruct (H1 e)=>//. apply/equivP. move/equivP : H.
intros.
apply:equiv_r_trans. apply/equiv_r_sym. 
apply:derive_pd_l.
apply:equiv_r_trans.  done.
apply:derive_pd_l. rewrite /Pb. apply/eqP. rewrite -!has_nuP2 in H2. done.
Qed.
End Extensional.
