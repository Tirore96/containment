From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
Require Import Relation_Definitions Setoid.
Require Import Coq.btauto.Btauto.
Require Import Paco.paco.
From Containment Require Import  tactics utils regex enum pred extensional_partial modules.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Let inE := tactics.inE.

Module Equivalence_on (M : FModule).
Module FM := EquivF M.
Module MyExt := ExtensionalPartial FM.
Import FM MyExt.
Implicit Types (r : @regex A).

Reserved Notation " l |- c0 =R= c1" (at level 63).
Inductive c_eq ( l : seq (@regex A  * regex)) : regex -> regex -> Prop :=
| c2_plus_assoc c0 c1 c2 : l |- (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
| c2_plus_comm c0 c1: l |- c0 _+_ c1 =R= c1 _+_ c0
| c2_plus_neut c : l |-  c _+_ Empt =R= c
| c2_plus_idemp c  : l |- c _+_ c =R= c 
| c2_seq_assoc c0 c1 c2  : l |- (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
| c2_seq_neut_l c : l |- (Eps _;_ c) =R= c 
| c2_seq_neut_r c : l |-  c _;_ Eps =R= c 
| c2_seq_failure_l c : l |- Empt _;_ c =R= Empt  
| c2_seq_failure_r c :  l |-c _;_ Empt =R= Empt 
| c2_distr_l c0 c1 c2 : l |- c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
| c2_distr_r c0 c1 c2 : l |- (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)

| c2_unfold c : l |-  Eps _+_ (c _;_ Star c) =R= Star c (*New star rule 1*)
| c2_star_plus c : l |-  Star (Eps _+_ c) =R= Star c (*New star rule 2*)
| c2_refl c : l |- c =R= c
| c2_sym c0 c1 (H: l |- c0 =R=c1) : l |- c1 =R=c0
| c2_trans c0 c1 c2 (H1 : l |- c0 =R=c1) (H2 : l |- c1 =R=c2) : l |- c0 =R=c2
| c2_plus_ctx c0 c0' c1 c1' (H1 : l |- c0 =R=c0') 
                             (H2 : l |- c1 =R=c1') : l |- c0 _+_ c1 =R=c0' _+_ c1'
| c2_seq_ctx c0 c0' c1 c1'  (H1 : l |- c0 =R=c0') 
                             (H2 : l |- c1 =R=c1') : l |-  c0 _;_ c1 =R=c0' _;_ c1'
| c2_star_ctx c0 c1         (H :  l |- c0 =R=c1) : l |- Star c0 =R= Star c1  (*new context rule*) 
| c2_var a c0 c1 : (c0, c1) \in l -> l |-  Event a _;_ c0 =R= Event a _;_ c1
| c2_fix c0 c1 :  (c0,c1)::l |- c0 =R= c1 ->  l |-  c0 =R= c1
(*| c_add r r' : (r,r')::l |- r =R= r'  -> l |- r =R= r'*)
 where "l |- c1 =R= c2" := (c_eq l c1 c2).
Hint Constructors c_eq.
Notation "c0 = ⟨ R ⟩ = c1" := (c_eq R c0 c1)(at level 63).


Add Parametric Relation R : regex (@c_eq R)
  reflexivity proved by (c2_refl R)
  symmetry proved by (@c2_sym R)
  transitivity proved by (@c2_trans R)
  as regex_setoid2.

Add Parametric Morphism R : Plus with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as c_eqc_plus_morphism2.
Proof.
intros. eauto. 
Qed.

Add Parametric Morphism R : Seq with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as co_eq_seq_morphism2.
Proof.
intros. eauto.
Qed.

Add Parametric Morphism R : Star with
signature (c_eq R) ==> (c_eq R) as c_eqc_star_morphism2.
Proof.
intros. eauto.
Qed.


Section CoInductive_Equivalence.
  Variable co_eq : @regex A -> @regex A -> Prop.
Reserved Notation "c0 =R= c1" (at level 63).
(*Maybe c_star_ctx and c_star_plus are not necessary*)

Inductive c_eqc : regex -> regex -> Prop :=
| c_plus_assoc c0 c1 c2 : (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)
| c_plus_comm c0 c1: c0 _+_ c1 =R= c1 _+_ c0
| c_plus_neut c: c _+_ Empt =R= c
| c_plus_idemp c : c _+_ c =R= c 
| c_seq_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
| c_seq_neut_l c : (Eps _;_ c) =R= c 
| c_seq_neut_r c : c _;_ Eps =R= c 
| c_seq_failure_l c : Empt _;_ c =R= Empt  
| c_seq_failure_r c :  c _;_ Empt =R= Empt 
| c_distr_l c0 c1 c2 : c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
| c_distr_r c0 c1 c2 : (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)

| c_unfold c :  Eps _+_ (c _;_ Star c) =R= Star c (*New star rule 1*)
| c_star_plus c :  Star (Eps _+_ c) =R= Star c (*New star rule 2*)
| c_refl c : c =R= c
| c_sym c0 c1 (H: c0 =R=c1) : c1 =R=c0
| c_trans c0 c1 c2 (H1 : c0 =R=c1) (H2 : c1 =R=c2) : c0 =R=c2
| c_plus_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _+_ c1 =R=c0' _+_ c1'
| c_seq_ctx c0 c0' c1 c1' (H1 : c0 =R=c0') (H2 : c1 =R=c1') : c0 _;_ c1 =R=c0' _;_ c1'
| c_star_ctx c0 c1 (H : c0 =R=c1) : Star c0 =R= Star c1  (*new context rule*) 
| c_fix a c0 c1 : co_eq c0 c1 ->  Event a _;_ c0 =R= Event a _;_ c1
 where "c1 =R= c2" := (c_eqc c1 c2).
End CoInductive_Equivalence.
Hint Constructors c_eqc.
Lemma c_eqc_gen_mon: monotone2 c_eqc. 
Proof.
unfold monotone2.
intros. induction IN; eauto. 
Qed.
Hint Resolve c_eqc_gen_mon : paco.
Notation "c0 = ⟪ R ⟫ = c1" := (c_eqc R c0 c1)(at level 63).
Definition EQ c0 c1 := paco2 c_eqc bot2 c0 c1.

Add Parametric Relation R : regex (@c_eqc R)
  reflexivity proved by (c_refl R)
  symmetry proved by (@c_sym R)
  transitivity proved by (@c_trans R)
  as regex_setoid.

Lemma EQ_refl : forall e, EQ e e.
Proof. move => e. pfold. con. Qed.

Lemma EQ_sym : forall e e', EQ e e' -> EQ e' e.
Proof. move => e e'. sunfold=>HQ. pfold. con=>//. Qed.

Lemma EQ_trans : forall e e' e'', EQ e e' -> EQ e' e'' -> EQ e e''.
Proof. move => e e' e''. sunfold=>HQ. sunfold=>HQ'. pfold. con=>//. eauto.  Qed.

Add Parametric Morphism R : Plus with
signature (c_eqc R) ==> (c_eqc R) ==> (c_eqc R) as c_eqc_plus_morphism.
Proof.
intros. eauto. 
Qed.

Add Parametric Morphism R : Seq with
signature (c_eqc R) ==> (c_eqc R) ==> (c_eqc R) as co_eq_seq_morphism.
Proof.
intros. eauto.
Qed.

Add Parametric Morphism R : Star with
signature (c_eqc R) ==> (c_eqc R) as c_eqc_star_morphism.
Proof.
intros. eauto.
Qed.

Section IndAx_to_CoAx.
(*For this proof the last case is most interesting, we have a choice btween c_fix and c_star_ctx,
  we choose c_star_ctx because we don't want to enter R
*)

Lemma c_eq_ind_coind_aux: forall (l : seq (regex * regex)) (R : regex -> regex -> Prop) c0 c1, c_eq l c0 c1 -> (forall x y, (x,y) \in l -> R x y)   -> paco2 c_eqc R c0 c1.
Proof.
move=> l R c0 c1 HC //=.
elim: HC R;ssa. 
pfold. apply:c_sym. pfold_reverse. 
pfold. apply:c_trans; pfold_reverse. 
pfold. apply:c_plus_ctx; pfold_reverse.
pfold. apply:c_seq_ctx;pfold_reverse.
pfold. apply:c_star_ctx;pfold_reverse.
pfold. apply:c_fix. eauto. 
pcofix CIH. apply:H0.
(*pfold. *)
(*apply:c_seq_ctx. done. pfold_reverse. pcofix CIH. apply:H0.*) (*we simulate rule c2_fix using pcofix to add a pair*)
intros. rewrite !inE in H0. de (orP H0). norm_eqs. inv H2. 
Qed.

(*inductive rules sound wrt to coinductive rules*)
Lemma c_eq_ind_coind: forall c0 c1, c_eq nil c0 c1 ->  EQ c0 c1. 
Proof.
intros. apply:c_eq_ind_coind_aux. eauto. done.
Qed.

End IndAx_to_CoAx.
Section CoAx_to_Bisim.

Lemma c_plus_neut_l : forall R c, Empt _+_ c =⟪R⟫= c.
Proof. intros. rewrite c_plus_comm. auto.
Qed.


Lemma c_eqc_nu : forall R (c0 c1 : regex) , c0 =⟪R⟫= c1 -> nu c0 = nu c1.
Proof. 
intros. induction H; simpl; auto with bool; try btauto.
all : try (rewrite IHc_eqc1; rewrite IHc_eqc2; auto).
Qed.

Lemma co_eq_nu : forall (c0 c1 : regex) , EQ c0 c1 -> nu c0 = nu c1.
Proof. 
intros. eapply c_eqc_nu. punfold H.
Qed.

Lemma plus_empt : forall (A: eqType) R (l : seq A), \big[Plus/Empt]_(a <- l) (Empt) = ⟪R⟫ = Empt.
Proof.
move=> B R. elim=>//=. rewrite big_nil //. 
move=> a l IH. rewrite big_cons IH //.
Qed.

Let eqs_aux :=   (c_plus_neut_l,
             c_plus_neut,
             c_seq_neut_l,
             c_seq_neut_r,
             c_seq_failure_l,
             c_seq_failure_r,
             c_distr_l,
             c_distr_r,c_plus_idemp).

Lemma o_plus : forall c0 c1 R, o (c0 _+_ c1) =⟪R⟫= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto. rewrite eqs_aux //.
Qed.

Lemma o_seq : forall c0 c1 R, o (c0 _;_ c1) =⟪R⟫= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto.
Qed.


(*Makes rewriting non-terminating*)
Lemma seq_comm_o : forall R c c', c _;_ (o c') =⟪R⟫= (o c') _;_ c.
Proof.
move=> R c c'. rewrite /o. case Hcase: (nu _)=>//; rewrite !eqs_aux //.
Qed.


Let eqs :=   (eqs_aux,o_plus,o_seq).

Ltac eq_m_leftc := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto.


Lemma co_eq_derive : forall (c0 c1 : regex) e, EQ c0 c1 -> EQ (e \ c0) (e \ c1).
Proof.
intros. pfold. punfold H. induction H; try solve [ simpl; rewrite ?eqs;auto] . 
- rewrite /=. case Hcase: (nu c0)=>//=. case Hcase1: (nu c1)=>//=; rewrite !eqs;eq_m_leftc. 
- rewrite /=; case Hcase:(nu _)=>//=; rewrite !eqs //.
- rewrite /=; case Hcase: (nu _)=>//;rewrite !eqs //.  
- rewrite /=; case Hcase: (nu _)=>//;rewrite !eqs //. eq_m_leftc. 
  rewrite c_plus_comm. eq_m_leftc.
- rewrite /=. case Hcase:(nu c0)=>//=;case Hcase':(nu c1)=>/=//;rewrite !eqs;eq_m_leftc. 
  rewrite {2}c_plus_comm -c_plus_assoc eqs c_plus_comm //. 
- rewrite /= eqs; case Hcase:(nu _)=>/=;rewrite  ?eqs //. 
- eauto.
- rewrite /=. 
  have: nu c0 = nu c0' by apply/c_eqc_nu; eauto. move=>->.
  case Hcase:(nu _)=>//=. eauto.  eauto. 
- rewrite /=. case Hcase: (_==_)=>//. rewrite !eqs //. case: H=>//=>H'. pfold_reverse.
  rewrite !eqs //.
Qed.

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

Lemma bisim_soundness : forall (c0 c1 : regex), EQ c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. 
intros. pfold. constructor.
- intros. right. apply CIH.  apply co_eq_derive. auto.
- rewrite /Pb /=. do 2 rewrite orbC /=.  apply/eqP. auto using co_eq_nu.
Qed.

Theorem equiv_r2 : forall c0 c1, Bisimilarity c0 c1 -> equiv_r c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. rewrite /Pb in HC'. 
  move/eqP: HC'=>HC'. ssa. do 2 rewrite orbC //= in HC'.
  rewrite !matchbP /matchb /= HC' //.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.

(*This direction is not necessary, so we omit it to highlight structure of the proof*)
(*Theorem equiv_r1 : forall c0 c1, equiv_r c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  rewrite /equiv_r. move=> s.  rewrite -!deriveP. eauto.
  move: (H0 nil). rewrite !matchbP /matchb /=.  
  move/eq_iff. intros.
  rewrite /Pb.  
  intros. apply/eqP. ssa. do 2 rewrite orbC //=. 
Qed.*)


(*Theorem equivP : forall c0 c1, equiv_r c0 c1 <-> Bisimilarity c0 c1.
Proof.
move=> c0 c1. con. apply/equiv_r1. apply/equiv_r2.
Qed.*)
End CoAx_to_Bisim.












(*Lemma derive_pd_l : forall (l : @pder A) e, equiv_r (e \ \big[Plus/Empt]_(i <- l) i) 
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
apply:derive_pd_l. rewrite /Pb. apply/eqP. 
rewrite /Pb in H2. move/eqP :H2=>H2. ssa. do 2 rewrite orbC /= in H2.
rewrite -!has_nuP2 in H2. done.
Qed.*)



Section AntimorovDecomp.

Lemma c2_plus_neut_l : forall R c, Empt _+_ c =⟨R⟩= c.
Proof. intros. rewrite c2_plus_comm. auto.
Qed.


Lemma plus_empt2 : forall (A: eqType) R (l : seq A), \big[Plus/Empt]_(a <- l) (Empt) = ⟨R⟩ = Empt.
Proof.
move=> B R. elim=>//=. rewrite big_nil //. 
move=> a l IH. rewrite big_cons IH //.
Qed.

Let eqs_aux2 :=   (c2_plus_neut_l,
             c2_plus_neut,
             c2_seq_neut_l,
             c2_seq_neut_r,
             c2_seq_failure_l,
             c2_seq_failure_r,
             c2_distr_l,
             c2_distr_r,c2_plus_idemp).

Lemma o_plus2 : forall c0 c1 R, o (c0 _+_ c1) =⟨R⟩= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto. rewrite eqs_aux2 //.
Qed.

Lemma o_seq2 : forall c0 c1 R, o (c0 _;_ c1) =⟨R⟩= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto.
Qed.

Lemma seq_comm_o2 : forall R c c', c _;_ (o c') =⟨R⟩= (o c') _;_ c.
Proof.
move=> R c c'. rewrite /o. case Hcase: (nu _)=>//; rewrite !eqs_aux2 //.
Qed.


Let eqs2 :=   (eqs_aux2,o_plus2,o_seq2).
Ltac eq_m_left2 := repeat rewrite c2_plus_assoc; apply c2_plus_ctx;
                 auto.
Ltac eq_m_right2 := repeat rewrite <- c2_plus_assoc; apply c2_plus_ctx;
                  auto.


Definition ex_eq  (l: seq A) (F0 F1 : A -> @regex A) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus : forall (l : seq A) F1 F2 R, ex_eq l F1 F2 (c_eq R) ->
   \big[Plus/Empt]_(i <- l) F1 i = ⟨R⟩ = \big[Plus/Empt]_(i <- l) F2 i.
Proof.
move=> + F1 F2 R. 
rewrite /ex_eq. elim=>//.
move=> _. rewrite !big_nil//.
move=> a l IH Hin. rewrite !big_cons. rewrite Hin //. 
eq_m_left2.
Qed.

(*Necessary to use ssreflect under for rewriting*)
Add Parametric Morphism R : (Under_rel regex (c_eq R)) with
signature (c_eq R ==> c_eq R ==> flip impl) as under_c_eq. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''. apply/c2_trans.  eauto. apply/c2_trans. eauto. apply/c2_sym. eauto.
Qed.

Add Parametric Morphism R : (Under_rel regex (c_eq R)) with
signature (c_eq R ==> c_eq R ==> impl) as under_c_eqc3. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''.  apply/c2_trans;last by eauto. apply/c2_trans;last by eauto. apply/c2_sym. eauto.
Qed.

(*This has to be proved by induction because I cannot use ssreflects big_split since commutativity is over c_eqc, and not leibniz equality*)
Lemma split_plus2 : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) = ⟨R⟩ = \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a).  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil // eqs2 //.
move=> a l IH. rewrite !big_cons. eq_m_left2. rewrite IH. eauto.
Qed.

Lemma factor_seq_l2 : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (c _;_ P a) =⟨R⟩=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)).
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil eqs2 //.
move=> a l IH. rewrite !big_cons eqs2 //= IH //.
Qed.

Lemma big_event_notin2 R : forall l a, a \notin l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) =⟨R⟩= Empt. 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //.
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite (negbTE Hneq) IH // !eqs2 //.
Qed.

Lemma big_event_in2 R : forall l a, a \in l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) =⟨R⟩= Event a. 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. move/orP. case. move/eqP=>Heq;subst.
rewrite big_cons eqxx //= !eqs2.
case Hcase: (a \in l). rewrite IH. apply/c2_plus_idemp=>//. rewrite Hcase//.
rewrite big_event_notin2 //. rewrite Hcase//.
move=>Hin. rewrite big_cons IH //.
case: (eqVneq a a0). move=>Heq;subst. rewrite !eqs2 //.
move=>Hneq. rewrite !eqs2 //=.
Qed.

Lemma derive_seq2 : forall R a r r', a \ (r _;_ r') =⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r').
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /= eqs2 //.
rewrite /o Hcase !eqs2 //.
Qed.

Lemma factor_seq_r2 : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (P a _;_ c) =⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c.
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil eqs2 //.
move=> a l IH. rewrite !big_cons eqs2 //= IH //.
Qed.


(*Why we need star ctx, 
  Proof below is by induction on regex syntax, to use IH, we need c0 = c1 -> c0* = c1*
  This cannot be derived, as we need some coinductive rule, namely c_fix, which requires
  us to show this decomposition rule to be useful
*)


(*Uses c_star_plus!*)
Lemma star_o2 : forall R c c', Star ((o c) _+_ c') =⟨R⟩ = Star c'.
Proof. 
move=> R c c'. 
rewrite /o. case Hcase: (nu c);last by rewrite eqs2 //. clear Hcase.
rewrite c2_star_plus //.
Qed.

Lemma derive_unfold2 : forall R c, c =⟨R⟩= o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c). 
Proof.
move=>R. 
elim.
- rewrite /o /=. under eq_big_plus. move=> a Hin. rewrite !eqs2. over. rewrite plus_empt2 eqs2 //.
- rewrite /o /=. under eq_big_plus. move=> a Hin. rewrite !eqs2. over. rewrite plus_empt2 eqs2 //.
- move => s. rewrite big_event_in2 /o //= ?eqs2 // mem_index_enum //. 
- move=> r HQ r' HQ'. rewrite o_plus2  /=. 
  under eq_big_plus. move=> a Hin. rewrite eqs2. over. 
  rewrite split_plus2. 
  apply/c2_trans. apply/c2_plus_ctx. apply: HQ. apply: HQ'. eq_m_left2.  
  rewrite c2_plus_comm. eq_m_left2.
- move=> r HQ r' HQ'. 
  under eq_big_plus. move=> a Hin. 
  rewrite derive_seq2 !eqs2 -!c2_seq_assoc seq_comm_o2 (c2_seq_assoc _ (o r)).
  over.
  rewrite split_plus2 !factor_seq_l2 !factor_seq_r2  o_seq2. 
  apply/c2_trans. apply/c2_seq_ctx. apply: HQ. apply: HQ'.
  apply/c2_trans. 2 : {  apply/c2_plus_ctx. apply/c2_refl. apply/c2_plus_ctx. apply/c2_seq_ctx. apply/c2_refl.
                        apply/c2_sym. apply: HQ'. apply/c2_refl. }
  rewrite !eqs2. eq_m_left2. 
- move=> r HQ /=. 
  under eq_big_plus. move=> a Hin. rewrite -c2_seq_assoc. rewrite {2}HQ. over.
  rewrite factor_seq_r2. rewrite {1}HQ.
  rewrite {1}star_o2.
  rewrite {1}star_o2. 
  rewrite c2_unfold. done.
 (*We need c_star_plus here*)
Qed.
End AntimorovDecomp.

Lemma c_eq_undup : forall l L,  \big[Plus/Empt]_(i <- (undup l)) i =⟨L⟩=  \big[Plus/Empt]_(i <- l) i.
Proof.
elim;ssa.
case_if. rewrite H. rewrite !big_cons. clear H.
elim: l a H0;ssa. 
rewrite !inE in H0. de (orP H0). norm_eqs. rewrite !big_cons. 
apply:c2_trans. 2: { apply:c2_trans.  2: { apply:c2_plus_assoc. }  apply:c2_plus_ctx. apply:c2_sym. apply:c2_plus_idemp. apply:c2_refl. } 
apply:c2_plus_ctx. done. done. rewrite !big_cons.
rewrite -c2_plus_assoc.
rewrite [a0 _+_ a] c2_plus_comm.
rewrite c2_plus_assoc. rewrite -(H a0) //. 
rewrite !big_cons.
apply:c2_plus_ctx. done. done.
Qed.

Lemma c_eq_cat : forall l0 l1 L,  \big[Plus/Empt]_(i <- l0 ++ l1) i =⟨L⟩=  \big[Plus/Empt]_(i <- l0) i _+_  \big[Plus/Empt]_(i <- l1) i.
Proof.
elim;ssa.
rewrite !big_nil. apply:c2_sym. apply:c2_trans. apply:c2_plus_comm. auto.
rewrite !big_cons. rewrite c2_plus_assoc. apply:c2_plus_ctx. done. done.
Qed.

Lemma c_eq_derive_pd_l : forall c L a, a \ c = ⟨ L ⟩ = \big[Plus/Empt]_(i <- pd a c) i.
Proof.
elim;ssa; try solve [ rewrite !big_nil //=].
case_if. norm_eqs. rewrite eqxx //= !big_cons big_nil.  auto.
rewrite eq_sym H big_nil //=.
rewrite c_eq_cat.
apply:c2_plus_ctx. done. done. 
case_if. rewrite c_eq_cat. apply:c2_plus_ctx.
rewrite map_big_plus.

rewrite factor_seq_r2. apply:c2_seq_ctx=>//. done. 
rewrite map_big_plus.
rewrite factor_seq_r2. apply:c2_seq_ctx=>//. 
rewrite map_big_plus.
rewrite factor_seq_r2. apply:c2_seq_ctx=>//. 
Qed.


Lemma decomp_p : forall l L,  \big[Plus/Empt]_(i <- l) i =⟨L⟩= (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof. 
intros. 
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

Lemma c_eq_mon : forall c0 c1 l l', c_eq l c0 c1 -> (is_sub l l') ->  c_eq l' c0 c1.
Proof.
intros. elim: H l' H0;ssa. 
apply:c2_trans. eauto. eauto.
apply:c2_fix. apply:H0.
intro. ssa. de (orP H0).
Qed.

Lemma o_lP : forall l l' L, has nu l = has nu l' ->  o_l l = ⟨ L ⟩ = o_l l'.
Proof.
intros. rewrite /o_l H. case_if;ssa.
Qed.

Fixpoint EQ_complete_aux p (V : seq (@pder A * @pder A)) (H : D_bisim V p) {struct H} : forall (L : seq (@regex A * @regex A)),
    (forall x y, (x,y) \in V ->  (\big[Plus/Empt]_(i <- x) i, \big[Plus/Empt]_(i <- y) i) \in L) -> 
                                                         reachable Pb H -> 
                                                         ((\big[Plus/Empt]_(i <- p.1) i), (\big[Plus/Empt]_(i <- p.2) i)) \in L \/
                                                         (\big[Plus/Empt]_(i <- p.1) i) =⟨L⟩= (\big[Plus/Empt]_(i <- p.2) i).
refine( match H with 
        | Db_stop x y z => _ 
        | _ => _ 
        end).
ssa.
left.
destruct (Utils.dec _). apply H0. destruct y. simpl. done.
clear H1;rewrite e // in z.
ssa. destruct (Utils.dec _). rewrite e in i. done. ssa. right.
apply c2_fix.
apply:c2_trans. apply:decomp_p. 
apply:c2_trans. 2: {  apply:c2_sym. apply:decomp_p. } 
apply:c2_plus_ctx. apply:(@c_eq_mon _ _ nil)=>//. apply:o_lP. 
rewrite /Pb in H2. apply/eqP. done.
destruct p1. ssa.
move  HeqL':  ((\big[Plus/Empt]_(i <- l) i, \big[Plus/Empt]_(i <- l0) i) :: L) => L'.
suff: forall a, Event a _;_  \big[Plus/Empt]_(i <- pd_l a l) i =⟨L'⟩= Event a _;_  \big[Plus/Empt]_(i <- pd_l a l0) i.
intros. clear H H2 H3 HeqL'.
move: H1.
move:(index_enum A)=> lA.
elim: lA. 
ssa. rewrite !big_nil. done.
ssa. rewrite !big_cons. apply:c2_plus_ctx.  done.
apply/H. done. 
intros.
move Heq : ( \big[Plus/Empt]_(i <- pd_l a l) i) => r0.
move Heq2 : ( \big[Plus/Empt]_(i <- pd_l a l0) i) => r1.
suff:    
(r0,r1) \in L' \/ r0 =⟨L'⟩=r1.
intros. destruct H1. apply:c2_var. done.
apply:c2_seq_ctx. done. done. 
move:(EQ_complete_aux _ _ (d a))=>//= HH. 
subst. apply HH. intros.
rewrite !inE in H1. de (orP H1). norm_eqs. inv H4. rewrite eqxx //. auto.
apply (allP H3). done.
Qed.

Lemma bisim_c_eq : forall l l', reachable_wrap l l' Pb ->  (\big[Plus/Empt]_(i <- l) i) =⟨nil⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. apply (@EQ_complete_aux _ _ _ nil) in H. destruct H. done. 
rewrite !c_eq_undup in H. done. rewrite /uniq_pair //=;ssa;apply:undup_uniq.
Qed.

Lemma equiv_r_plus : forall (c0 c1 : @regex A), equiv_r c0 c1 -> equiv_r (\big[Plus/Empt]_(i <- c0::nil) i)  (\big[Plus/Empt]_(i <- c1::nil) i).
Proof.
intros. intro. ssa. rewrite !big_cons !big_nil. split;ssa. inv H0;eauto. con. apply/H. done. inv H3.
inv H0. con. apply/H. done. inv H3.
Qed.

Lemma c_eq_soundness : forall (c0 c1 : regex), c0 =⟨nil⟩= c1 ->  equiv_r c0 c1.
Proof. move=> c0 c1. move/c_eq_ind_coind. move/bisim_soundness. move/equiv_r2=>//.
Qed.

Lemma c_eq_completeness : forall (c0 c1 : regex), equiv_r c0 c1 -> c0 =⟨nil⟩= c1.
Proof. move=> c0 c1. move/equiv_r_plus. move/Bisim_co_ind. move/bisim_complete.
move/bisim_c_eq. rewrite !big_cons !big_nil. eauto.
Qed.



Lemma dslF_plus_shape : forall a R x y, dslF R (\big[Plus/Empt]_(e <- a::nil) ((Event e) _;_ x))
                                    (\big[Plus/Empt]_(e <- a::nil) ((Event e) _;_ y)) -> dslF R (Event a _;_ x) 
                                                                                             (Event a _;_ y).
Proof.
intros. rewrite !big_cons !big_nil in X.
eauto.
Qed.

Definition fold_back : forall (r0 r1 : @regex A), dsl_co r0 r1 -> dslF dsl_co r0 r1.
Proof.
intros. inv X.
Defined.






End Equivalence_on.


