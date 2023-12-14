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
From Containment Require Import  utils regex pred.
Set Implicit Arguments.
Set Maximal Implicit Insertion.


(*Module Extensional (M : Pred).
Include M.

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


Theorem equiv_rInd : forall l l', Extensional l l' -> forall s, P s ( (\big[Plus/Empt]_(i <- l) i))  (\big[Plus/Empt]_(i <- l') i).
Proof.
move=> l0 l1 HC s. 
elim: s l0 l1  HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'.
  apply Pb_P_iff. done.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. 
  apply/P_derive. apply IH. done.
Qed.

Theorem Bisim_co_ind : forall l l', (forall s, P s (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i)) -> Extensional l l'.
Proof.
pcofix CIH. move=> l l'. pfold. con. 
intros. right. apply:CIH. intros.
apply P_derive. apply H0.
apply/Pb_P_iff. done.
Qed.

Lemma Extensional_equiv : forall l l', Extensional l l' <->  forall s, P s (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i). 
Proof.
intros. split. apply/equiv_rInd. apply:Bisim_co_ind.
Qed.


Unset Implicit Arguments.

(*Less effecient, fix this later*)  
Equations bisim (pp : pder * pder) (visited : seq (pder * pder) ) : bool by wf (r_measure visited pp) := 
 bisim pp visited  with (dec (pp \in visited)) => {
  bisim _  _ (in_left) := true;
  bisim pp visited (in_right) with (dec (uniq_pair pp)) => { 
        bisim pp visited _ (in_left) := (Pbl pp.1 pp.2) && 
                                        (foldInAll (index_enum A) (fun e _ => bisim (pair_pd_l e (pp)) (pp::visited)));
        bisim pp visited _ (in_right) := false }
 }.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.

(*Effecient but awkard for proofs*)
Equations bisim2 (pp : pder * pder) (visited : seq (pder * pder) ) (H : uniq_pair pp) : bool by wf (r_measure visited pp) := 
 bisim2 pp visited H  with (dec (pp \in visited)) => {
  bisim2 _  _ _ (in_left) := true;
  bisim2 pp visited _ (in_right) := (Pbl pp.1 pp.2) && 
                                           (foldInAll (index_enum A) (fun e _ => bisim2 (pair_pd_l e pp) (pp::visited) _));
 }.
Next Obligation. 
apply/andP.
con. simpl. rewrite /pd_l. done.  simpl. rewrite /pd_l. done.
Defined.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
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


Definition undup2 (pp : pder * pder) := (undup pp.1,undup pp.2).
Lemma pair_uniq_proof : forall (pp : pder*pder), uniq_pair (undup2 pp). 
Proof.
intros. rewrite /uniq_pair. ssa.
Qed.
Definition bisim_wrap (l l' : pder) := bisim2 (undup l,undup l') nil (pair_uniq_proof (l,l')).



(*Check pd_plus.
Lemma pd_plus : forall l a, pd a (\big[Plus/Empt]_(i <- l) i) = flatten (map (pd a) l).*)
Theorem equiv_rInd : forall l l', Extensional l l' -> equiv_r ( (\big[Plus/Empt]_(i <- l) i))  (\big[Plus/Empt]_(i <- l') i).
Proof.
move=> l0 l1 HC s. 
elim: s l0 l1  HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. 
  rewrite -!Match_has_nu_iff. HC' //.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. 
  rewrite !deriveP2. rewrite /pd_sum. rewrite !pd_plus //.
  apply/IH=>//. 
Qed.

Lemma Extensional_equiv : forall l l', Extensional l l' <->  equiv (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i). 
Proof.
intros. split. apply/equiv_rInd. move/equivP/Bisim_co_ind=>//.
Qed.

Lemma bisim_complete : forall l0 l1, Extensional l0 l1 ->  bisim_wrap l0 l1.
Proof.
intros. apply:bisim_complete_aux2. 
apply/Extensional_equiv. 
intro. rewrite !Match_big_undup. move: s. apply/Extensional_equiv=>//.
Qed.









End Extensional.*)

(*Lemma nu_has : forall l, nu (\big[Plus/Empt]_(i <- l) i) = has nu l.
Proof.
elim;ssa.
rewrite big_nil. done. rewrite !big_cons /=. f_equal. done.
Qed.*)

(*Definition equiv_r (r0 r1 : regex) := forall s, Match s r0 <-> Match s r1.

Lemma equiv_r_derive : forall r0 r1 e, equiv_r r0 r1 -> equiv_r (e \ r0) (e \ r1).
Proof.
intros. intro. rewrite -!deriveP. done.
Qed.
Lemma equiv_r_trans : forall r0 r1 r2, equiv_r r0 r1 -> equiv_r r1 r2 -> equiv_r r0 r2.
Proof.
intros. intro. rewrite H -H0 //.
Qed.

Lemma equiv_r_sym : forall r0 r1, equiv_r r0 r1 -> equiv_r r1 r0. 
Proof.
intros. intro. rewrite H //.
Qed.
*)


(*elim;ssa. rewrite !big_nil. done.
rewrite !big_cons. split;intros; ssa.
rewrite /pd_l. simpl. 
rewrite Match_big_undup. 
rewrite Match_big_cat. 
inv H0.
con.
rewrite -Match_big_undup. 
have:  (\big[Plus/Empt]_(i <- undup (pd e a)) i) = pd_sum e a. done.
move=>->. rewrite -deriveP2. rewrite -deriveP in H3. done.
constructor 5. 
apply H in H3. rewrite /pd_l in H3. rewrite Match_big_undup in H3. done.

rewrite /pd_l Match_big_undup /= Match_big_cat in H0.
inv H0. con. rewrite -deriveP deriveP2 /pd_sum Match_big_undup //.
constructor 5. apply/H.  rewrite /pd_l Match_big_undup //.
Qed.*)

(*Definition pder := seq regex.
Implicit Type (l : pder).
Lemma Match_has_nu : forall l, has nu l ->  Match [::] (\big[Plus/Empt]_(i <- l) i).
Proof.
elim;ssa. de (orP H0). rewrite !big_cons /=. con.
apply:Match_nil_nu. done.
rewrite !big_cons. constructor 5. eauto.
Qed.


*)
(*End Regex.
Arguments regex {A}.
Arguments Eps {A}.
Arguments Empt {A}.
Arguments Event {A}.
Arguments Plus {A}.
Arguments Seq {A}.
Arguments Star {A}.
Notation "s \\ c" := (trace_derive s c)(at level 42, no associativity).
Notation "s \ c" := (derive s c)(at level 42, no associativity).
Notation "c0 _;_ c1"  := (Seq c0 c1)
                         (at level 52, left associativity).

Notation "c0 _+_ c1"  := (Plus c0 c1)
                         (at level 53, left associativity).
*)





Module Bisim (p: Pred).
Include p.
Inductive bisimilarity_gen bisim : regex -> regex -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: Pb c0 c1) : bisimilarity_gen bisim c0 c1.

Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.


Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.

Hint Resolve bisimilarity_gen_mon : paco.


(*Parameter bisimilarity_gen bisim : regex -> regex -> Prop. *)
(*:=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: Pb c0 c1) : bisimilarity_gen bisim c0 c1.*)

Parameter Bisimilarity c0 c1 : regex -> regex -> Prop. 
(*:= paco2 bisimilarity_gen bot2 c0 c1.*)
(*Hint Unfold  Bisimilarity : core.*)


(*Axiom bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.*)

(*Hint Resolve bisimilarity_gen_mon : paco.*)
End Pred.

Module myPred : Pred.
Check (unit : finType).
Definition A := Datatypes_unit__canonical__fintype_Finite.
Definition P (r0 r1 : @regex A) := forall s, Match s r0 <-> Match s r1.
Definition Pb (r0 r1 : @regex A) := (nu r0 == nu r1).

Implicit Type (r : regex).




End myPred.




Module TestModule (MP : Pred).
Import MP.  
(*Parameter (P: regex -> regex -> Prop).
Parameter (Pb : regex -> regex -> bool).*)

Definition pder := seq regex.

Fixpoint pd a r := 
match r with 
| Eps => nil 
| Empt => nil 
| Event a' => if a == a' then Eps::nil else nil
| Plus r0 r1 => (pd a r0) ++ (pd a r1)
| Seq r0 r1 => if nu r0 then (map (fun x => Seq x r1) (pd a r0)) ++ (pd a r1) else (map (fun x => Seq x r1) (pd a r0))
| Star r0 => map (fun x => x _;_ Star r0) (pd a r0)
end.

Definition pd_l a l := undup (flatten (map (pd a) l)).


Inductive exten_gen bisim : pder -> pder-> Prop :=
 contains_con2 l0 l1 (H0: forall e, bisim (pd_l e l0) (pd_l e l1) : Prop ) (H1: Pbl l0 l1) : exten_gen bisim l0 l1.

Definition BisimInd l0 l1 := paco2 exten_gen bot2 l0 l1.
Hint Unfold  BisimInd : core.

Lemma exten_gen_mon: monotone2 exten_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve exten_gen_mon : paco.






































End TestModuel.






(*
Module Type Simulation (p : Pred).
Include p.
Definition regex := @regex p.A.
Inductive bisimilarity_gen bisim : regex -> regex -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: Pb c0 c1) : bisimilarity_gen bisim c0 c1.

Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.


Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.

Hint Resolve bisimilarity_gen_mon : paco.

Axiom P_iff_Bisim : forall c0 c1, P c0 c1 <-> Bisimilarity c0 c1.
End Simulation.*)


Module Simulation (p : Pred).
Include p.
Definition regex := @regex p.A.
Inductive bisimilarity_gen bisim : regex -> regex -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: Pb c0 c1) : bisimilarity_gen bisim c0 c1.

Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.


Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.

Hint Resolve bisimilarity_gen_mon : paco.
End Simulation.



Module M := Simulation1 myPred.
Print M.x
Print Assumptions.
End Simulation1.
(*Theorem equiv_r1 : forall c0 c1, equiv_r c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  rewrite /equiv_r. move=> s.  rewrite -!deriveP. eauto.
  move: (H0 nil). rewrite !matchbP /matchb /=. 
  move/eq_iff=>->//.
Qed.*)

(*Theorem equiv_r2 : forall c0 c1, Bisimilarity c0 c1 -> equiv_r c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. rewrite !matchbP /matchb /= HC' //.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.*)


(*Theorem equivP : forall c0 c1, equiv_r c0 c1 <-> Bisimilarity c0 c1.
Proof.
move=> c0 c1. con. apply/equiv_r1. apply/equiv_r2.
Qed.*)








































(*Maybe put and inductive derivation here as well*)
Section ExampleDerivations.
Lemma c_trans1: forall c0 c1 c2 co_eq,
     c0 = ⟪co_eq⟫= c1 ->
       c1 = ⟪co_eq⟫= c2 -> c0 = ⟪co_eq⟫= c2.
Proof. eauto. Qed.

Lemma c_trans2 : forall c0 c1 c2 co_eq,
       c1 = ⟪co_eq⟫= c2 ->  c0 = ⟪co_eq⟫= c1 ->
       c0 = ⟪co_eq⟫= c2.
Proof. eauto. Qed.

Ltac tc1 := apply:c_trans1.
Ltac tc2 := apply:c_trans2.
Ltac tcs H := apply:c_sym;apply:H.
Ltac ap H := apply:H.
Ltac tr := apply:c_refl.
Ltac tp := apply:c_plus_ctx.

Lemma star_aux : forall a R, Star (Star (Event a)) =⟪R⟫= Eps _+_  ((Event a) _;_ (Star (Event a)) _;_ (Star (Star (Event a)))).
Proof.
intros. 
tc1. apply:c_star_ctx. tcs c_unfold.
tc1. apply:c_star_plus.
tc1. tcs c_unfold. 
tp. done. 
tc1. apply: c_seq_assoc.
tc2. tcs c_seq_assoc.
apply:c_seq_ctx.  done.
apply:c_seq_ctx. done.
tc1. tcs c_star_plus.
tc1. apply:c_star_ctx. apply:c_unfold. 
done.
Qed.


Lemma star_star_co_eq : forall a, EQ (Star (Event a))  (Star (Star (Event a))).
Proof.
intros. pfold.
tc1.  tcs c_unfold.
tc2. apply:c_sym. apply:star_aux.
apply:c_plus_ctx.  done.
tc2. tcs c_seq_assoc. 
apply:c_seq_ctx. done.
pfold_reverse. pcofix CIH. pfold.
tc1. tcs c_unfold.
tc2. apply:c_seq_ctx. apply:c_unfold. tr.
tc2. tcs c_distr_r.
tc2. tp. tcs c_seq_neut_l. tr.
tc2. apply:c_plus_ctx. apply:c_sym. apply:star_aux. tr.
tc2. tcs c_plus_assoc.
tp. done.
tc2.
tcs c_plus_idemp.
tc2. tcs c_seq_assoc.
apply:c_fix. right. apply/CIH.
Qed.

End ExampleDerivations.























Section Equivalence_Soundness.




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
Definition o c := if nu c then Eps else Empt.

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
intros. pfold. punfold H. induction H; try solve [ simpl; rewrite ?eqs;eauto] . 
- rewrite /=. case Hcase: (nu c0)=>//=. case Hcase1: (nu c1)=>//=; rewrite !eqs;eq_m_leftc. 
- rewrite /=; case Hcase:(nu _)=>//=; rewrite !eqs //.
- rewrite /=; case Hcase: (nu _)=>//;rewrite !eqs //.  
- rewrite /=; case Hcase: (nu _)=>//;rewrite !eqs //. eq_m_leftc. 
  rewrite c_plus_comm. eq_m_leftc.
- rewrite /=. case Hcase:(nu c0)=>//=;case Hcase':(nu c1)=>/=//;rewrite !eqs;eq_m_leftc. 
  rewrite {2}c_plus_comm -c_plus_assoc eqs c_plus_comm //. 
- rewrite /= eqs; case Hcase:(nu _)=>/=;rewrite  ?eqs //. 
- rewrite /=. 
  have: nu c0 = nu c0' by apply/c_eqc_nu; eauto. move=>->.
  case Hcase:(nu _)=>//=. eauto.  eauto. 
- rewrite /=. case Hcase: (_==_)=>//. rewrite !eqs //. case: H=>//=>H'. pfold_reverse.
  rewrite !eqs //.
Qed.

Inductive bisimilarity_gen bisim : regex -> regex -> Prop :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: nu c0 = nu c1) : bisimilarity_gen bisim c0 c1.

Definition Bisimilarity c0 c1 := paco2 bisimilarity_gen bot2 c0 c1.
Hint Unfold  Bisimilarity : core.


Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.

Hint Resolve bisimilarity_gen_mon : paco.

Definition equiv_r (r0 r1 : regex) := forall s, Match s r0 <-> Match s r1.

Theorem equiv_r1 : forall c0 c1, equiv_r c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  rewrite /equiv_r. move=> s.  rewrite -!deriveP. eauto.
  move: (H0 nil). rewrite !matchbP /matchb /=. 
  move/eq_iff=>->//.
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

Lemma bisim_soundness : forall (c0 c1 : regex), EQ c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. 
intros. pfold. constructor.
- intros. right. apply CIH.  apply co_eq_derive. auto.
- auto using co_eq_nu.
Qed.


Lemma c_eq_soundness : forall (c0 c1 : regex),  c0 =⟨nil⟩= c1 -> Bisimilarity c0 c1.
Proof.
intros. apply/bisim_soundness. apply/c_eq_ind_coind=>//.
Qed.


End Equivalence_Soundness.
Hint Resolve bisimilarity_gen_mon : paco.


Section AntimorovDecomp.

Lemma c2_plus_neut_l : forall R c, Empt _+_ c =⟨R⟩= c.
Proof. intros. rewrite c2_plus_comm. auto.
Qed.


Lemma plus_empt2 : forall (A: eqType) R (l : seq A), \big[Plus/Empt]_(a <- l) (Empt) = ⟨R⟩ = Empt.
Proof.
move=> B R. elim=>//=. rewrite big_nil //. 
move=> a l IH. rewrite big_cons IH //.
Qed.

Let eqs_aux :=   (c2_plus_neut_l,
             c2_plus_neut,
             c2_seq_neut_l,
             c2_seq_neut_r,
             c2_seq_failure_l,
             c2_seq_failure_r,
             c2_distr_l,
             c2_distr_r,c2_plus_idemp).


Lemma o_plus2 : forall c0 c1 R, o (c0 _+_ c1) =⟨R⟩= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto. rewrite eqs_aux //.
Qed.

Lemma o_seq2 : forall c0 c1 R, o (c0 _;_ c1) =⟨R⟩= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto.
Qed.

Lemma seq_comm_o2 : forall R c c', c _;_ (o c') =⟨R⟩= (o c') _;_ c.
Proof.
move=> R c c'. rewrite /o. case Hcase: (nu _)=>//; rewrite !eqs_aux //.
Qed.


Let eqs2 :=   (eqs_aux,o_plus2,o_seq2).
Ltac eq_m_left2 := repeat rewrite c2_plus_assoc; apply c2_plus_ctx;
                 auto.
Ltac eq_m_right2 := repeat rewrite <- c2_plus_assoc; apply c2_plus_ctx;
                  auto.


Definition ex_eq {A : eqType} (l: seq A) (F0 F1 : A -> regex) R  := forall a, a \in l -> R (F0 a) (F1 a).

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

(*Shorten this proof*)
Lemma derive_seq2 : forall R a r r', a \ (r _;_ r') =⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r').
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /= eqs2 //.
rewrite /o Hcase !eqs2 //.
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




Section DecideBismim.

Fixpoint enum (A : Type) (n : nat) (R : seq A) := 
match n with 
| 0 => nil::nil 
| n'.+1 => (compose R (enum n' R) cons)++(enum n' R)
end.


Lemma in_enum_nil : forall (A : eqType) n (R : seq A), nil \in enum n R. 
Proof.
move=> A'.
elim;ssa.
rewrite mem_cat H. lia.
Qed.


Lemma in_enum : forall (A : eqType) n R (l : seq A), size l <= n -> (forall x, x \in l -> x \in R) -> l \in enum n R. 
Proof.
move=> A'.
elim;ssa. destruct l;ssa.
destruct l. rewrite mem_cat in_enum_nil. lia.
rewrite mem_cat. apply/orP. left.
apply/mem_compose. eauto. eauto.
Qed.

Lemma uniq_size : forall (A : eqType) (l : seq A) R, uniq l -> (forall x, x \in l -> x \in R) -> size l <= size R.
Proof.
move=> A'.
elim;ssa. 
have : forall x, x \in l -> x \in R. eauto.
move=> Hin. 
move: (H _ H3 Hin). move=>Hsize.
move: (H1 a). rewrite !inE /=. move/(_ is_true_true)=>Hr.
apply:size_strict_sub. done. done. eauto. done.
Qed.

Lemma in_enum_uniq : forall (A : eqType) R (l : seq A), uniq l -> (forall x, x \in l -> x \in R) -> l \in enum (size R) R. 
Proof.
intros. apply:in_enum.  apply:uniq_size. done. done. done.
Qed.

Lemma mem_compose_cons : forall (B : eqType) (aa : seq B) bb l,   l \in compose aa bb cons -> exists a b, l = cons a b /\  a \in aa /\ b \in bb.
Proof. move => B. elim;intros. done. 
move : H0=>/=. rewrite mem_cat. move/orP. case. move/mapP=>[] //=. intros. inversion q. subst. 
econ. econ.  eauto.

move/H. case. ssa. subst. econ. econ. eauto.
Qed.


Lemma enum_inR : forall (A : eqType) n R (l : seq A) x, l \in enum n R -> x \in l -> x \in R. 
Proof.
move=> A'.
elim;ssa. rewrite !inE in H. norm_eqs. done.
rewrite mem_cat in H0. de (orP H0). 
apply mem_compose_cons in H2. ssa. subst. 
rewrite !inE in H1. de (orP H1). norm_eqs. done.
eauto.
eauto.
Qed.


Fixpoint pi r := 
match r with 
| Eps => nil
| Empt => nil 
| Event _ => Eps::nil
| Plus r0 r1 =>  (pi r0) ++ (pi r1) 
| Seq r0 r1 => (map (fun x => x _;_ r1)(pi r0)) ++ (pi r1) 
| Star r0 => map (fun x => x _;_ Star r0 )(pi r0)
end.
Definition pi2 r := r::(pi r).





Ltac lo := match goal with 
                | [H : is_true (_ || _) |- _] => destruct (orP H);norm_eqs;try solve [ssa]
                end.


Lemma pi_d : forall r r' a, r' \in pd a r -> r' \in pi r.
Proof.
elim;ssa. move: H. case_if. done. done.
rewrite mem_cat in H1.  rewrite mem_cat. apply/orP. lo; eauto. 
destruct (nu _) eqn:Heqn. rewrite !mem_cat in H1 *. apply/orP. lo. 
destruct (mapP H2). subst. left. apply/map_f;  eauto. eauto.
destruct (mapP H1). subst. rewrite mem_cat. apply/orP. left. apply/map_f. eauto.
destruct (mapP H0). subst.  apply/map_f. eauto.
Qed.
Hint Resolve pi_d.

Hint Resolve map_f.
Lemma in_pi_pd : forall r0 r1 r2 a, r1 \in pi r0 -> r2 \in pd a r1 -> r2 \in pi r0.
Proof.
elim;ssa.
- rewrite !inE in H. norm_eqs. ssa. 
- rewrite !mem_cat in H1 *.  destruct (orP H1).  
  move: (H _ _ _ H3 H2). ssa. 
  move: (H0 _ _ _ H3 H2). ssa. 
- rewrite !mem_cat in H1 *. 
  destruct (orP H1). destruct (mapP H3). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H2. destruct (orP H2).
  destruct (mapP H5). subst. 
  move: (H _ _ _ H4 H6). ssa. 
  con. apply/map_f. done. eauto. 
  destruct (mapP H2). subst. 
  move: (H _ _ _ H4 H5). ssa.
  left. apply/map_f. eauto.
  move: (H0 _ _ _ H3 H2). ssa.  
- destruct (mapP H0). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H3). subst.
  move: (H _ _ _ H2 H4). ssa. 
  apply/map_f. eauto.
  destruct (mapP H3). subst. apply:map_f. eauto.
  destruct (mapP H1). subst. ssa.
  move: (H _ _ _ H2 H3). ssa. apply/map_f. eauto.
Qed.

Lemma in_pd_pi : forall r0 r1 r2 a, r1 \in pd a r0 -> r2 \in pi r1 -> r2 \in pi r0.
Proof.
elim;ssa.
- move:H. rifliad. norm_eqs. rewrite !inE. intros. norm_eqs. ssa.
- rewrite !mem_cat in H1 *.  destruct (orP H1).  
  move: (H _ _ _ H3 H2). ssa. 
  move: (H0 _ _ _ H3 H2). ssa. 
- rewrite !mem_cat in H1 *. 
(*  destruct (orP H1). destruct (mapP H3). subst. ssa.*)
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H1. destruct (orP H1).
  destruct (mapP H3). subst. ssa.
  rewrite mem_cat in H2. de (orP H2). de (mapP H5). subst.
  move: (H _ _ _ H4 H6). ssa. 
  con. apply/map_f. done. eauto. 
  move: (H0 _ _ _ H3 H2). ssa. de (mapP H1). subst. ssa.
  rewrite mem_cat in H2. de (orP H2). de (mapP H4). subst. ssa.
  move: (H _ _ _ H3 H5). ssa. left. apply/map_f. done.
- destruct (mapP H0). subst. ssa.
  rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H3). subst.
  move: (H _ _ _ H2 H4). ssa. 
  apply/map_f. eauto.
  destruct (mapP H3). subst. apply:map_f. eauto.
Qed.

Lemma in_pi2_pd : forall r0 r1 r2 a, r1 \in pi2 r0 -> r2 \in pd a r1 -> r2 \in pi2 r0.
Proof.
intros. rewrite !inE in H. lo. rewrite !inE. apply/orP. right. eauto.
rewrite !inE. apply/orP. right. apply/in_pi_pd. eauto. eauto.
Qed.

Lemma in_pd_pi2 : forall r0 r1 r2 a, r1 \in pd a r0 -> r2 \in pi2 r1 -> r2 \in pi2 r0.
Proof.
intros. rewrite !inE in H0. lo. rewrite !inE. apply/orP. right. eauto.
rewrite !inE. apply/orP. right. apply/in_pd_pi. eauto. eauto.
Qed.

Definition pi_l (l : seq regex) := undup (flatten (map pi2 l)).
Definition enum_pi l := (enum (size (pi_l l)) (pi_l l)).
Definition enum_pi2 l := map undup (enum_pi l). 






Lemma in_pd_enum_aux : forall (l l' : seq regex) a, l' \in  enum_pi2 (pd_l a l) ->  l' \in enum_pi l.
Proof.
intros. 
apply:in_enum_uniq. de (mapP H). subst. apply:undup_uniq.
intros. ssa. rewrite /enum_pi2 in H.
de (mapP H). subst.
rewrite /pi_l. rewrite mem_undup. 
apply/flattenP. simpl. rewrite mem_undup in H0.

move: (@enum_inR _ _ _ _ _ H1 H0).
move=>Hin. rewrite /pi_l in Hin. rewrite mem_undup in Hin.
de (flattenP Hin). de (mapP H2). subst. 
rewrite /pd_l in H4. rewrite mem_undup in H4. de (flattenP H4). de (mapP H5). subst.
econ. apply/map_f. 
2: { apply:in_pd_pi2.  apply:H6.  done. } 
done.
Qed.

Lemma in_pd_enum : forall (l l' : seq regex) a, l' \in  enum_pi2 (pd_l a l) ->  l' \in enum_pi2 l.
Proof.
intros. move: (in_pd_enum_aux _ _ _ H). intros.
de (mapP H). subst.
apply/mapP. econ.  eauto. symmetry. rewrite undup_id //.
apply/undup_uniq.
Qed.

Lemma enum_pi_self : forall l, uniq l ->  l \in enum_pi l.
Proof.
intros. apply:in_enum_uniq. done.
intros. rewrite /pi_l. rewrite mem_undup.
apply/flattenP. simpl. econ. 
apply/map_f. eauto. rewrite !inE //.
Qed.

Lemma enum_pi2_self : forall l, uniq l ->  l \in enum_pi2 l.
Proof.
intros. apply enum_pi_self in H as H'. 
rewrite /enum_pi2. apply/mapP. econ. eauto. 
rewrite undup_id //.
Qed.
Hint Resolve enum_pi2_self.


Definition pair_enum ee := utils.compose (enum_pi2 ee.1) (enum_pi2 ee.2) pair. 
Definition pair_pd_l a (ee : pder * pder) := (pd_l a ee.1,pd_l a ee.2).

Definition uniq_pair (pp : pder * pder) := uniq pp.1 && uniq pp.2.
Lemma selfee : forall pp, uniq_pair pp ->  pp \in pair_enum pp. 
Proof. case. intros. rewrite /uniq_pair in H. ssa.
rewrite /pair_enum /=. apply/mem_compose;eauto.
Qed.
Hint Resolve selfee.

Lemma in_pd_pair_enum : forall l l' a, l' \in  pair_enum (pair_pd_l a l) ->  l' \in pair_enum l.
Proof.
intros. rewrite /pair_enum in H.  rewrite /pair_enum. destruct l'.
apply mem_compose2 in H. destruct H. ssa.
destruct l. ssa. 
apply/mem_compose. 
apply:in_pd_enum. apply:H.
apply:in_pd_enum. apply:H0.
Qed.



Definition r_measure ( visited : seq (pder * pder)) (l : pder * pder) := 
size (rep_rem visited (undup (pair_enum l))). 


(*Used in session type project*)
Lemma measure_lt : forall V l a, uniq_pair l -> l \notin V -> r_measure (l::V) (pair_pd_l a l) < r_measure V l.
Proof.
move=> V l a Hun Hnotin.
intros. rewrite /r_measure. 
simpl. 
destruct (l \in (pair_enum (pair_pd_l a l))) eqn:Heqn.
- apply/size_strict_sub.
 * apply/rem_uniq/rep_rem_uniq/undup_uniq. (*uniqueness not interesting*)
 * intros. destruct (eqVneq x l). (* enum e0 \ e::visited <= enum e \ visited *) (*x \in left -> x \in right*)
  **  subst. rewrite -mem_rep_iff.  rewrite mem_undup. eauto. (*x = e and \e \notin visited so x \in enum e \ visited*) (*have: uniq l. de (mapP Heqn). subst. apply:undup_uniq. move=>Hun.
      apply/pair_enum_self. done.*) done. 
  ** apply mem_rem2 in H;eauto. (*x != e*)
     have : x \notin V. apply/negP=>HH. eapply rep_rem_uniq2 in HH.

     2: { instantiate (1:= undup (pair_enum (pair_pd_l a l))).  done. }
     rewrite H //= in HH. move => Heqn2.
     move : H. rewrite -!mem_rep_iff;eauto. (*x \notin V so x \in enum e0 -> x \in enum e by main lemma*)
     rewrite  !mem_undup. intros. apply/in_pd_pair_enum. eauto.
 * instantiate (1 := l).  apply/negP=>HH. rewrite mem_rem_uniqF in HH. done. (*e \notin enum e0 \ e::V*)
   apply/rep_rem_uniq/undup_uniq. 
 * rewrite -mem_rep_iff.  rewrite mem_undup. eauto.  done.
(*apply/pair_enum_self. 
   have: uniq l. de (mapP Heqn). subst. apply:undup_uniq=>//. done. done.*)
- have :  l \notin rep_rem V (undup (pair_enum (pair_pd_l a l))). 
  apply/negP=>HH. move : Heqn. move/negP=>H2. apply/H2. 
  apply/mem_rep_iff.  apply:Hnotin. apply/rep_rem2. done.
  2 :  eauto.  intros. rewrite mem_undup in H. done. move => HH'. 

  rewrite rem_id //=. (*e \notin enum e0, suff to show enum e0 \ V < enum e \ V *)
  apply/size_strict_sub;eauto.   
  * apply/rep_rem_uniq. apply/undup_uniq. (*uniquenes not interesting*)
  * intros. have : x \notin V. apply/negP=>HH. eapply rep_rem_uniq2 in HH. 
    2: {  instantiate (1:= undup (pair_enum (pair_pd_l a l))).  done. }
    rewrite H //= in HH. move => Heqn2. (*x \notin V*)
    move : H. rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. 
    apply:in_pd_pair_enum. eauto. done. done.
(*    rewrite Heqn2. (*suff to show x \in enum e0 -> x \in enum e by main lemma*)
    done. rewrite Heqn2. done.*)
  * rewrite -mem_rep_iff. rewrite mem_undup. eauto. done.
Qed.


Unset Implicit Arguments.

(*Less effecient, fix this later*)
Equations bisim (pp : pder * pder) (visited : seq (pder * pder) ) : bool by wf (r_measure visited pp) := 
 bisim pp visited  with (dec (pp \in visited)) => {
  bisim _  _ (in_left) := true;
  bisim pp visited (in_right) with (dec (uniq_pair pp)) => { 
        bisim pp visited _ (in_left) := ((has nu pp.1) == (has nu pp.2)) && 
                                        (foldInAll (index_enum A) (fun e _ => bisim (pair_pd_l e (pp)) (pp::visited)));
        bisim pp visited _ (in_right) := false }
 }.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.

(*Effecient but awkard for proofs*)
Equations bisim2 (pp : pder * pder) (visited : seq (pder * pder) ) (H : uniq_pair pp) : bool by wf (r_measure visited pp) := 
 bisim2 pp visited H  with (dec (pp \in visited)) => {
  bisim2 _  _ _ (in_left) := true;
  bisim2 pp visited _ (in_right) := ((has nu pp.1) == (has nu pp.2)) && 
                                           (foldInAll (index_enum A) (fun e _ => bisim2 (pair_pd_l e pp) (pp::visited) _));
 }.
Next Obligation. 
apply/andP.
con. simpl. rewrite /pd_l. done.  simpl. rewrite /pd_l. done.
Defined.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
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

Lemma bisim_complete_aux : forall l0 l1 l_v, uniq_pair (l0,l1) ->  BisimInd l0 l1 ->  bisim  (l0,l1) l_v.  
Proof. 
intros. funelim (bisim  (l0,l1) l_v).  rewrite -Heqcall. ssa.
rewrite -Heqcall. ssa. 
punfold H1.  inv H1. apply/eqP=>//.
rewrite foldInAllP. apply/allP=> x xIn. 
apply:H. apply/inP. eauto.  simpl. 
rewrite /uniq_pair /pd_l. ssa.
punfold H1. inv H1. case: (H2 x)=>//. con. 
done. rewrite  e1 in H. done.
Qed.


Definition bisim_wrap (l l' : pder) := bisim2 (undup l,undup l') nil.

Lemma bisim_complete : forall l0 l1, BisimInd l0 l1 ->  bisim_wrap l0 l1.
Proof.
intros. apply:bisim_complete_aux. rewrite /uniq_pair. ssa.
apply/BisimInd_equiv. 
intro. rewrite !Match_big_undup. move: s. apply/BisimInd_equiv=>//.
Qed.

End DecideBismim.




Inductive pTree : regex -> Type := 
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

Lemma pTree_Match : forall r T, typing T r -> Match (uflatten T) r.  
Proof.
move => r T. elim;ssa. inv H. inv H2. inv H2.  con. done. done.
Qed.

Definition contains (r0 r1 : regex) := forall s, Match s r0 -> Match s r1.

Definition constr_eps_coerce r0 r1 (H : contains r0 r1): pTree r0 -> pTree r1 := 
fun T =>  (proj1_sig (Match_pTree (H _ (pTree_Match (to_typing T))))).

Lemma constr_eps_coerce_pres_string : forall r0 r1 (H : contains r0 r1) (T : pTree r0), pflatten (constr_eps_coerce  H T) = pflatten T. 
Proof.
intros. rewrite /constr_eps_coerce /=. 
destruct ((Match_pTree (H (uflatten (to_upTree T)) (pTree_Match (to_typing T))))) eqn:Heqn.
simpl. rewrite (eqP i). rewrite uflatten_to_upTree //.
Qed.

End CoercionByConstructiveEpsilon.



Require Import MSets.MSetRBT. 
Locate color.

Require Import MSets Arith.
Locate Nat_as_OT.
Locate  OrderedTypeEx.Nat_as_OT.
Check OrderedTypeEx.Nat_as_OT.

(* We can make a set out of an ordered type *)
Module S := Make Nat_as_OT

Section DSL.
Check PTree.tree.
Definition tree_add  (A' : Type) (r : PTRee.tree A) (k := 
Inductive dsl (R: PTree.tree (regex * regex)) : regex -> regex -> Type := 
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
| dsl_var a A B n : PTree.get n R = Some (A,B) -> dsl R ((Event a) _;_ A) ((Event a) _;_ B) 
(*| dsl_var A B :   (A,B) \in R -> dsl R (Event a A) ( B) *)

(*without summation as that was due to productivity checker, not needed for inductive definition*)

| dsl_fix A B n : PTree.get n R = None -> dsl (PTree.set n (A,B) R) A B -> dsl R A B.
(**)
End DSL.
Notation "c0 < ⟨ R ⟩ = c1" := (dsl R c0 c1)(at level 63).

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

Definition is_sub_bool {A : eqType} (l0 l1 : seq A) := all (fun x => x \in l1) l0.
Lemma is_subP : forall (A : eqType) (l0 l1 : seq A), is_sub l0 l1 <-> is_sub_bool l0 l1.
Proof.
intros. split. 
rewrite /is_sub. intros. apply/allP. intro. eauto.
move/allP.  eauto.
Qed.


(*Lemma dsl_mon : forall l l' E F, dsl l E F -> is_sub_bool l l' ->  dsl l' E F.
Proof.
move=> l l' E F p. 
elim: p l';auto with dsl;simpl;intros.
apply:ctrans. eauto. eauto.
apply:dsl_var. move/is_subP : H=>Hsub. apply Hsub. done.
apply:dsl_fix. apply:X. ssa.
apply/is_subP. move/is_subP : H.
intro. intro. move/H. rewrite !inE. move=>->//. lia.
Defined.*)


(*Benefit about this derivation is there is no duplication of 
 dsl both in rules and syntax, here it is the same, thus no need for unfolding*)
Definition tree := PTree.empty (regex * regex).
Lemma dsl_example : forall a, dsl tree  (Star (Star (Event a))) (Star (Event a)).
Proof.
move=> a.  

apply: ctrans=>//. apply: cstar=>//. apply: wrapinv=>//.

apply/ctrans=>//. apply/drop=>//.
apply/ctrans=>//. apply/wrapinv=>//.
apply/ctrans=>//. 2: { apply/wrap=>//. }
apply/cplus=>//. apply/cid=>//.
apply/ctrans=>//. apply/assoc=>//.
(*apply/guard=>//. left. pcofix CIH. pfold*)  

(*Just like cseq_ctx which was used in c_ineq we do the same now before applying dsl_fix. 
  Before the dsl_fix rule also 
  We went from event (e _;_ c, e _;_ c') step to (c,c') 
  and then remember (c,c') using cofix.
  This step is simulated by dsl by applying dsl_fix now
 *)
apply/cseq=>//. apply/cid=>//. (*Don't use rule_guard yet*) (*apply/rule_guard=>//. left=>//. pfold.*)

apply:(dsl_fix xH). done.


(*pfold_reverse. pcofix CIH. pfold.*) (*pcofix before cfix*)
(*apply/rule_cfix=>//. simpl=>//. *)

apply: ctrans.  (*rewrite /full_unf //=. *)
apply/cseq=>//. apply/cid=>//. apply/dropinv=>//.

apply/ctrans=>//. apply/cseq=>//. apply/cid=>//. apply/cstar/wrap=>//. 

(*again we apply dsl_fix instead of pcofix*)
apply:(dsl_fix (xO xH)). done.
(*pfold_reverse=>//. pcofix CIH2=>//. pfold=>//.*) (*pcofix before cfix*)
(*apply/cfix=>//. simpl=>//. *)



apply/ctrans. (*rewrite /full_unf //=. *) apply/cseq=>//. apply/wrapinv=>//. apply/cid=>//.
apply/ctrans=>//. apply/distR=>//.
apply/ctrans=>//. apply/cplus=>//. apply/proj=>//. apply/cid=>//.
apply/ctrans=>//. 2: { apply/drop=>//. }
apply/ctrans=>//. 2: { apply/wrap=>//. }

apply/ctrans=>//. 2: { apply/cplus=>//. apply/cid=>//. apply/cseq=>//. apply/cid=>//. apply/dropinv=>//. }
apply/ctrans=>//. 2: { apply/cplus=>//. apply/cid=>//. apply/distRinv=>//. }




apply/ctrans=>//. 2: { apply/cplus=>//. apply/cid=>//. apply/cplus=>//. apply/projinv=>//. apply/cid=>//. }
apply/ctrans=>//. 2: { apply/retag=>//. }
apply/ctrans=>//. 2: { apply/tagL=>//. }


apply/cplus=>//. 

apply/ctrans=>//. apply/cstar/wrapinv=>//. 
apply/ctrans=>//. apply/drop=>//.
apply/ctrans=>//. apply/wrapinv=>//.
apply/ctrans=>//. 2: { apply/wrap=>//. }
apply/cplus=>//. apply/cid=>//.
apply/ctrans=>//. apply/assoc=>//.
apply:(dsl_var xH)=>//.
(*exact:(dsl_var 1). *)
(*apply/guard=>//. right. apply/CIH.*)

apply/ctrans=>//. apply/assoc=>//.

apply:(dsl_var (xO xH))=>//. 
(*exact:(dsl_var 0). *)
(*apply/guard=>//. right.  apply/CIH2.*)
Qed.




Section InductiveInterpretation.





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

Lemma regex_dec : forall (x y : regex), { x = y} + { x <> y }.
Proof. 
intros. de (eqVneq x y)=>//. constructor 2. apply/eqP=>//.
Qed.

Check regex_dec.
Check Eqdep_dec.eq_rect_eq_dec.
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
         (f : forall n x y, PTree.get n l = Some (x,y) -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) {struct p}:
  post r1 T. 
refine(
match p in dsl _ x y return r0 = x -> r1 = y -> post r1 T  with
| dsl_fix r0 r1 n H p0 => fun HQ HQ' => _ (*Do at least one case to force coq to destruct *)
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
have:  (forall n x y ,
        PTree.get n l = Some (x, y) -> forall T0 : pTree x, pRel0 T0 T' -> post y T0).
intros. eapply f. eauto. move: H0. rewrite /pRel0. ssa. lia. move=>Hf. 
case: (interp _ _ _ d0 T' Hf)=>T2 HT2.  
exists T2. ssa. lia. rewrite H2 H0 //.

move: (interp _ _ _ d)=>H0.  
move: (interp _ _ _ d0)=>H1.  

dp T f. 
have: (forall n x y, PTree.get n l = Some (x, y) -> forall T0 : pTree x, pRel0 T0 p -> post y T0).
intros. eapply f. eauto. done. 
move=>Hf0. 
case: (H0 p Hf0)=>T0 HT0.  
exists (p_inl T0)=>//. 

have: (forall n x y, PTree.get n l = Some (x, y) -> forall T0 : pTree x, pRel0 T0 p -> post y T0).
intros. eapply f. eauto. done. move=>Hf.
case: (H1 p Hf)=>T1 HT1. 
exists (p_inr T1)=>//. 

move: (interp _ _ _ d)=>H0.
move: (interp _ _ _ d0)=>H1. 
dp T f.
have: (forall n x y, PTree.get n l = Some (x, y) -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).
intros. eapply f. eauto. move: H2. rewrite /pRel0 //=. lia. move=>Hf0.
have: (forall n x y, PTree.get n l = Some (x, y) -> forall T0 : pTree x, pRel0 T0 p1 -> post y T0).
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
have: (forall n x y, PTree.get n l = Some (x, y) -> forall T0 : pTree x, pRel0 T0 p0 -> post y T0).
intros. eapply f. eauto. move: H0. rewrite /pRel0 //=. lia. 
move=>Hf.
case: (interp p0 Hf)=> x Hx. 
have: pRel1 p1 (p_fold (p_inr (p_pair p0 p1))). rewrite /pRel1 //=. move: (pTree_1size1 p0). lia.
move=>Hsize.
have: (forall n x0 y,
    PTree.get n l = Some (x0, y) -> forall T0 : pTree x0, pRel0 T0 p1 -> post y T0).
intros. eapply f. eauto. move: H0. rewrite /pRel0 /=.  lia.
move=>Hf'.
case: (X p1 Hsize interp Hf')=>x' Hx'. 
exists (p_fold (p_inr (p_pair x x'))). ssa. lia. rewrite H0 H2//.

dp T f. dp p1 f. 
have : pRel0 p2 (p_pair (p_singl s) p2). rewrite /pRel0 /=. lia.
move=>Hrel.
move: (f _ _ _ e p2 Hrel). case. move=> x Hflat. ssa. 
exists (p_pair (p_singl s) x). 
ssa. f_equal. done. 

move : T f.
eapply (@pTree_0size_rect r0 (fun (T : pTree r0) => (forall n x y, PTree.get n l = Some (x,y) -> forall (T0 : pTree x), pRel0 T0 T -> post y T0) -> post r1 T)).
move=> Hin IH Hf.
eapply (@interp _ _ _ p0 Hin). 
intros.
destruct (Pos.eqb n0 n) eqn:Heqn.
move/Pos.eqb_spec:Heqn=>HH. subst.
rewrite PTree.gss in H0.
case: H0. intros;subst.

eapply IH. apply H1.  
move=> n' x' y' Hl T1 Hrel. eapply Hf. apply Hl. 
move: H1 Hrel. rewrite /pRel0. lia. 
simpl in H. 
move/Pos.eqb_spec:Heqn=>HH. 
rewrite PTree.gso in H0=>//.
eapply Hf. apply H0. apply H1.
Defined.



Lemma dsl_sound : forall c0 c1, dsl tree c0 c1 -> (forall s, Match s c0 -> Match s c1).
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

Section DSL_Complete.

(*Lemma unf0 d : mu_height d = 0 -> full_unf d = d. 
Proof.
rewrite /full_unf. move=>->//. 
Qed.
Ltac t0 := exact:unf0.

Hint Resolve unf0.*)



(*Definition proj_proof {A : Type} {P : A -> Prop}  (H : { x| P x}) : P (proj_sig H)  :=
match H with 
| exist x H => H
end.*)
Ltac pp := intros;apply:proj2_sig.
Hint Constructors dsl.
Lemma o_plus_l : forall c0 c1 R, (o (c0 _+_ c1)) <⟨R⟩= (o c0 _+_ o c1).
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto. 
Qed.

(*Lemma o_plus_l : forall c0 c1 R, (o (c0 _+_ c1)) <(R)= (o c0 _+_ o c1) ~> (proj_sig (o_plus_l c0 c1 R)).
Proof. pp. Qed.*)

Lemma o_plus_r : forall c0 c1 R, (o c0 _+_ o c1)  <⟨R⟩=  (o (c0 _+_ c1)).
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto. 
Qed.

(*Lemma o_plus_r : forall c0 c1 R, (o c0 _+_ o c1)  <⟨R⟩=  (o (c0 _+_ c1)) ~> (proj_sig (o_plus_r c0 c1 R)).
Proof. pp. Qed.*)


Lemma o_seq_l : forall c0 c1 R,  o (c0 _;_ c1) <⟨R⟩= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.

(*Lemma o_seq_l: forall c0 c1 R, o (c0 _;_ c1) <⟨R⟩= o c0 _;_ o c1 ~> (proj_sig (o_seq_l c0 c1 R)).
Proof. pp. Qed.*)

Lemma o_seq_r : forall c0 c1 R, o c0 _;_ o c1 <⟨R⟩=  o (c0 _;_ c1) .
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;eauto.
Qed.

(*Lemma o_seq_r : forall c0 c1 R, o c0 _;_ o c1 <⟨R⟩=  o (c0 _;_ c1) ~> (proj_sig (o_seq_r c0 c1 R)).
Proof. pp. Qed.*)


Ltac bt H := apply:H.

Lemma ctrans1
     : forall c0 P c1 c2,
       c0 < ⟨P⟩= c1 -> c1 < ⟨P⟩= c2  ->  c0 <⟨P⟩= c2.
Proof.
intros. apply:ctrans;eauto.
Qed.

Lemma ctrans2
     : forall c0 P c1 c2,
       c1 < ⟨P⟩= c2 ->  c0 < ⟨P⟩= c1 -> c0 < ⟨P⟩= c2.
Proof.
intros. apply:ctrans;eauto.
Qed.

Lemma cplus1
     : forall c0 c0' P c1 c1',
       c0 < ⟨P⟩= c0' -> c1 < ⟨P⟩= c1' ->  c0 _+_ c1 < ⟨P⟩= c0' _+_ c1'. 
Proof.
intros. apply:cplus;eauto.
Qed.

Lemma cplus2
     : forall  c0 c0' P c1 c1',
       c1 < ⟨P⟩= c1' ->  c0 < ⟨P⟩= c0' ->   c0 _+_ c1 < ⟨P⟩= c0' _+_ c1'. 
Proof.
intros. apply:cplus;eauto.
Qed.

Lemma cseq1
     : forall c0 c0' c1 c1' P,
       c0 < ⟨P⟩= c0' ->
       c1 < ⟨P⟩= c1' ->  c0 _;_ c1 < ⟨P⟩= c0' _;_ c1'.
Proof. intros. apply:cseq;eauto.
Qed.

Lemma cseq2
     : forall c0 c0' c1 c1' P,
    c1 < ⟨P⟩= c1' ->
       c0 < ⟨P⟩= c0'  ->c0 _;_ c1 < ⟨P⟩= c0' _;_ c1'. 
Proof. intros. apply:cseq;eauto.
Qed.

Lemma cstar1
     : forall c0 c1 P,
      c0 < ⟨P⟩= c1 ->  Star c0 < ⟨P⟩= Star c1. 
Proof. intros. apply:cstar;eauto.
Qed.


Ltac lct1 := apply:ctrans1.
Ltac lct2 := apply:ctrans2.
Ltac lcid := bt cid.
Ltac lcp1 := apply:cplus1.
Ltac lcp2 := apply:cplus2.
Ltac lcs1 := apply:cseq1.
Ltac lcs2 := apply:cseq2.
Ltac lcst1 := apply:cstar1.
Print dsl.
Lemma split_plus_l : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) <⟨R⟩= \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a) .  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:shuffle.
lct2. apply:shuffleinv. lcp1. lcid.
lct2. lct2. apply:retag. apply:shuffleinv. 
lcp1. lcid. eauto.
Qed.

(*Lemma split_plus_l : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) <⟨R⟩= \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a) 
                                                                               (proj2_sig (split_plus_l R B l P P')).  
Proof. pp. Qed.*)

Lemma split_plus_r : forall R (B: eqType) l (P P' : B -> regex), 
 \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a)  <⟨R⟩=     \big[Plus/Empt]_(a <- l) (P a _+_ P' a) .  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:shuffle. lct2. apply:shuffleinv. lcp1.  lcid.
lct1. lct1. apply:retag. apply:shuffle. 
lcp1. lcid. eauto.
Qed.

(*Lemma split_plus_r : forall R (B: eqType) l (P P' : B -> regex), 
 \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a)  <⟨R⟩=     \big[Plus/Empt]_(a <- l) (P a _+_ P' a) (proj_sig (split_plus_r R B l P P')).  
Proof. pp. Qed.*)

Lemma factor_seq_l_l : forall R (B: eqType) l (P: B -> regex) c,   
\big[Plus/Empt]_(a <- l) (c _;_ P a) <⟨R⟩=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)) .
Proof.
move=> R B +P c. elim=>//=. econ. rewrite !big_nil //. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons //=.
lct2. apply:distLinv. lcp1. lcid. eauto. 
Qed.

(*Lemma factor_seq_l_l : forall R (B: eqType) l (P: B -> regex) c, 
\big[Plus/Empt]_(a <- l) (c _;_ P a) <⟨R⟩=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)) (proj_sig (factor_seq_l_l R B l P c)).
Proof. pp. Qed.*)


Lemma factor_seq_l_r : forall R (B: eqType) l (P: B -> regex) c,   
c _;_ (\big[Plus/Empt]_(a <- l) (P a)) 
<⟨R⟩=  
\big[Plus/Empt]_(a <- l) (c _;_ P a) 
.
Proof.
move=> R B +P c. elim=>//=. econ. rewrite !big_nil //. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons //=. 
lct1. apply:distL. lcp1. lcid. eauto. 
Qed.

(*Lemma factor_seq_l_r : forall R (B: eqType) l (P: B -> regex) c,
c _;_ (\big[Plus/Empt]_(a <- l) (P a)) 
<⟨R⟩=  
\big[Plus/Empt]_(a <- l) (c _;_ P a) 
(proj_sig (factor_seq_l_r R B l P c)).
Proof. pp. Qed.*)


Lemma factor_seq_r_l : forall R (B: eqType) l (P: B -> regex) c,  
\big[Plus/Empt]_(a <- l) (P a _;_ c) <⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c .
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct2. apply:distRinv. eauto. 
Qed.

(*Lemma factor_seq_r_l : forall R (B: eqType) l (P: B -> regex) c, 
\big[Plus/Empt]_(a <- l) (P a _;_ c) <⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c (proj_sig (factor_seq_r_l R B l P c)).
Proof. pp. Qed.*)

Lemma factor_seq_r_r : forall R (B: eqType) l (P: B -> regex) c,  
(\big[Plus/Empt]_(a <- l) (P a)) _;_ c 
<⟨R⟩= 
\big[Plus/Empt]_(a <- l) (P a _;_ c) . 
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons. 
lct1. apply:distR. eauto. 
Qed.

(*Lemma factor_seq_r_r : forall R (B: eqType) l (P: B -> regex) c, 
(\big[Plus/Empt]_(a <- l) (P a)) _;_ c 
<⟨R⟩= 
\big[Plus/Empt]_(a <- l) (P a _;_ c) (proj_sig (factor_seq_r_r R B l P c)). 
Proof. pp. Qed.*)



Lemma eps_c_r : forall r R,   r < ⟨R⟩= r _;_ Eps.
Proof.
intros. econ. lct2. apply:swapinv. eauto. done. done.
Qed.
(*Lemma eps_c_r : forall r R, r < ⟨R⟩= r _;_ Eps (proj_sig (eps_c_r r R)). 
Proof. pp. Qed.*)
Hint Resolve eps_c_r.

Lemma eps_c_l : forall r R,   r _;_ Eps < ⟨R⟩= r .
Proof.
intros. econ. lct1. apply:swap. eauto. eauto.
Qed.

(*Lemma eps_c_l : forall r R, r _;_ Eps < ⟨R⟩= r  (proj_sig (eps_c_l r R)).
Proof. pp. Qed.*)
Hint Resolve eps_c_l.
(*Lemma eps_c_l : forall r R,   Eps _;_ r < ⟨R⟩= r  d }.
Proof.
intros. econ. eauto. 
Qed.*)




Definition ex_coerce {A : eqType} (l: seq A) (F0 F1 : A -> regex) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus_c : forall (l : seq A) F1 F2 R, ex_coerce l F1 F2 (dsl R) ->
   \big[Plus/Empt]_(i <- l) (F1 i) <⟨R⟩= \big[Plus/Empt]_(i <- l) (F2 i). 
Proof.
move=> + F1 F2 R. 
rewrite /ex_coerce. elim=>//.
move=> _. rewrite !big_nil//. 
move=> a l IH Hin. rewrite !big_cons /=. lcp1. apply:Hin. done.
eauto. 
Qed.

(*Add Parametric Morphism R : (Under_rel regex (c_ineq R)) with
signature (c_ineq R ==> c_ineq R ==> flip impl) as under_c_ineq. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''. apply/c_trans.  eauto. apply/c_trans. eauto. apply/c_sym. eauto.
Qed.*)

Lemma derive_seq_l : forall R a r r', a \ (r _;_ r') <⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') .
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /=. 
lcp1. lcid. eauto. 
rewrite /o Hcase /=.  eauto.
Qed.

(*Lemma derive_seq_l : forall R a r r', a \ (r _;_ r') <⟨R⟩= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') (proj_sig (derive_seq_l R a r r')) .
Proof. pp. Qed.*)

Lemma derive_seq_r : forall R a r r', 
((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') 
 <⟨R⟩= 
a \ (r _;_ r')
.
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /=. 
lcp1. lcid. eauto. 

rewrite /o Hcase /=.  lct1. lct1. lcp1. lcid. apply:abortL. apply:retag. eauto. 
Qed.

(*Lemma derive_seq_r : forall R a r r', 
((a \ r) _;_ r') _+_ (o (r) _;_ a \ r') 
 <⟨R⟩= 
a \ (r _;_ r')
(proj_sig (derive_seq_r R a r r')).
Proof. pp. Qed.*)


Lemma com_seq_o_l : forall R r r', o(r) _;_ r' <⟨R⟩= r' _;_ o(r) .
Proof.
intros. rewrite /o. case Heq:(nu _)=>//=. eauto.  
Qed.

(*Lemma com_seq_o_l : forall R r r',  o(r) _;_ r' <⟨R⟩= r' _;_ o(r) (proj_sig (com_seq_o_l R r r')).
Proof. pp. Qed.*)

Lemma com_seq_o_r : forall R r r', r' _;_ o(r)  <⟨R⟩=  o(r) _;_ r' .
Proof.
intros. rewrite /o. case Heq:(nu _)=>//=. eauto.  
Qed.

(*Lemma com_seq_o_r : forall R r r',  r' _;_ o(r)  <⟨R⟩=  o(r) _;_ r' (proj_sig (com_seq_o_r R r r')).
Proof. pp. Qed.*)


Lemma plus_empt_l : forall (A: eqType) R (l : seq A),  \big[Plus/Empt]_(a <- l) (Empt) <⟨R⟩ = Empt .
Proof.
move=> B R. elim=>//=. rewrite big_nil //. 
move=> a l IH. rewrite big_cons. lct2. apply:untag. lcp1. lcid. eauto.
Qed.

(*Lemma plus_empt_l : forall (A: eqType) R (l : seq A), \big[Plus/Empt]_(a <- l) (Empt) <⟨R⟩ = Empt (proj_sig (plus_empt_l A R l)).
Proof. pp. Qed.*)


Lemma big_event_notin_l R : forall l a, a \notin l ->   \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Empt . 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //. 
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite (negbTE Hneq).  move: (IH _ Hin). intros.
lct2. apply:untag. lcp1. eauto. eauto. 
Qed.

(*Lemma big_event_notin_l R : forall l a (H : a \notin l), \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Empt (proj_sig (big_event_notin_l R l a H)). 
Proof. pp. Qed.*)

Lemma big_event_notin_r R : forall l a, a \notin l -> Empt  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a))  . 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //. eauto.
Qed.

(*Lemma big_event_notin_r R : forall l a (H: a \notin l),  Empt  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a))  (proj_sig (big_event_notin_r R l a H)). 
Proof. pp. Qed.*)


Lemma empt_r_c : forall c R,  c _+_ Empt < ⟨R⟩= c .
Proof. eauto.
Qed.
(*Lemma empt_r_c : forall c R,  c _+_ Empt < ⟨R⟩= c (proj_sig (empt_r_c c R)).
Proof. pp. Qed.
Hint Resolve empt_r_c.*)

Lemma big_event_in_l R : forall l a, a \in l ->  \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Event a . 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. destruct (a0 == a) eqn:Heqn. move=>_.
move/eqP : Heqn=>Heq;subst.
rewrite big_cons eqxx //=. 
case Hcase: (a \in l). 
move: (IH _ Hcase). intros. lct2. apply:untag. lcp1. eauto. eauto. 
lct1. lcp1. apply:eps_c_l. apply:big_event_notin_l. 
rewrite Hcase. done.  eauto. 
simpl. intro. move: (IH _ H). intros. 
rewrite big_cons Heqn. lct1. lcp1. eauto.  eauto. eauto. 
Qed.

(*Lemma big_event_in_l R : forall l a (H : a \in l), \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) <⟨R⟩= Event a (proj_sig (big_event_in_l R l a H)). 
Proof. pp. Qed.*)

Lemma big_event_in_r R : forall l a, a \in l -> Event a  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) . 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. destruct (a0 == a) eqn:Heqn. move=>_.
move/eqP : Heqn=>Heq;subst.
rewrite big_cons eqxx //=. 
case Hcase: (a \in l). 
move: (IH _ Hcase). intros. lct2.  apply:tagL. eauto. 
have: a \notin l. by lia.
move=>HH. lct2.  apply:tagL. eauto. 
simpl. move=>HH.
move: (IH _ HH). intros. rewrite big_cons /= Heqn.
lct2. apply:retag. lct2. apply:tagL. eauto. 
Qed.

(*Lemma big_event_in_r R : forall l a (H : a \in l), Event a  <⟨R⟩= \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) (proj_sig (big_event_in_r R l a H)). 
Proof.
pp. 
Qed.*)

(*Uses drop!*)
Lemma star_o_l : forall R c c', Star (o (c) _+_ c') <⟨R⟩ = Star c' .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.
(*Lemma star_o_l : forall R c c', Star (o (c) _+_ c') <⟨R⟩ = Star c' (proj_sig (star_o_l R c c')).
Proof. pp. Qed.*)

Lemma star_o_r : forall R c c', Star c' <⟨R⟩ =  Star (o (c) _+_ c') .
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c)=>//. eauto.
Qed.

(*Lemma star_o_r : forall R c c', Star c' <⟨R⟩ =  Star (o (c) _+_ c') (proj_sig (star_o_r R c c')).
Proof. pp. Qed.*)

Lemma derive_unfold_coerce : forall c, dsl (PTree.empty _) c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c))  *
                                   dsl (PTree.empty _) (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c.
Proof.
elim;try solve [eauto].
- con. eauto. rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 
- con. eauto. rewrite /o /=. lct2. lct2. apply:untagL. apply:retag. 
  lcp1. lcid. lct1.  apply:eq_big_plus_c. intro. intros. apply:abortR. apply: plus_empt_l. 

- move=> s. con.
 *  rewrite /o /=. lct2. apply:retag. lct2. apply:tagL. 
    apply:big_event_in_r. rewrite mem_index_enum //. 
 *  rewrite /o /=. lct1. apply:untagL. apply:big_event_in_l. rewrite mem_index_enum //. 
- move=> r0 [] Hd0 Hd0' r1 [] Hd1 Hd1'. econ.
(*[] d1 Hd1 [] d1' Hd1'. econ.*)
 * 
   lct1. lcp1. apply:Hd0. apply:Hd1. 
   lct1. apply:shuffle. lct2. lcp1. apply: o_plus_r. lcid. 
   lct2. apply:shuffleinv. lcp1. lcid. 
   lct1. lct1. apply:retag. apply:shuffle. 
   lcp1. lcid. simpl. 
   lct2. apply:eq_big_plus_c. intro. intros. apply:distLinv.
   lct2. lct2.  apply:split_plus_r.  apply:retag. 
   lcp1. lcid. lcid. 
 * 
   lct2. lcp2. apply:Hd1'. apply:Hd0'. 
   lct2. apply:shuffleinv. lct1. lcp1. apply: o_plus_l. lcid. 
   lct1. apply:shuffle. lcp1. lcid. simpl. 
   lct1. lcp1. lcid. lct1. apply:eq_big_plus_c. intro. intros. apply:distL. 
   apply split_plus_l. 
   lct1. lct1. apply:retag. apply:shuffle. lcp1. lcid.
   lct1. apply:retag. eauto. 
- move=> r0 [] Hd0 Hd0' r1 [] Hd1 Hd1'. econ.

(*- move=> r0 [] [] d0 Hd0 [] d0' Hd0' r1 [] [] d1 Hd1 [] d1' Hd1'. econ.*)
  * 
    lct2. lcp1. apply: o_seq_r. 
    lct2. apply: eq_big_plus_c. intro. intros. lct2. lcs1. lcid. apply:derive_seq_r.
    lct2. apply:distLinv. lct2. lcp1. lct2. apply:assoc. lcs1. lcid. apply:Hd1'.
    lct2. lcs1. lcid. apply:com_seq_o_r. apply:assoc. lcid.
    lct2. apply: split_plus_r. lct2. lcp1.
    lct2. apply:factor_seq_r_r.  apply:distLinv. apply: factor_seq_r_r. lcid.
    lct1. lcs1. apply: Hd0. apply: Hd1.
    lct1. apply:distR.
    lct1. lcp1. apply:distL. apply:distL.
    lct1. apply:shuffle. lcp1. lcid.
    lct2. apply:retag. lcp1. apply:com_seq_o_l.
    lcp1. eauto. eauto. 
  * econ. 
    lct1. lcp1. apply: o_seq_l. 
    lct1. apply: eq_big_plus_c. intro. intros. lct1. lcs1. lcid. apply:derive_seq_l.
    lct1. apply:distL. lct1. lcp1. lct1. apply:associnv. lcs1. lcid. apply:Hd1.
    lct1. lcs1. lcid. apply:com_seq_o_l. apply:associnv. lcid.
    lct1. apply: split_plus_l. lct1. lcp1.
    lct1. apply:factor_seq_r_l.  apply:distL. apply: factor_seq_r_l. lcid.
    lct2. lcs1. apply: Hd0'. apply: Hd1'.
    lct2. apply:distRinv.
    lct2. lcp2. apply:distLinv. apply:distLinv.
    lct2. apply:shuffleinv. lcp1. lcid.
    lct2. apply:retag. lcp1. lcid. apply:com_seq_o_r. done.
    
- move=> r0 [] Hd Hd'. con.  
  * lct2. lcp1. lcid. simpl. lct2. 
    apply:eq_big_plus_c. intro. intros. lct2. apply:assoc. lcs1. lcid.
    lcst1. apply/Hd'. 
    apply:factor_seq_r_r. 
    lct1. lct1. lcst1. apply: Hd. apply: star_o_l.
    rewrite {1}/o /=.
    lct2. lcp1. lcid. lcs1. lcid. apply: star_o_r. eauto.  
  *  lct1. lcp1. lcid. simpl. lct1. 
    apply:eq_big_plus_c. intro. intros. lct1. apply:associnv. lcs1. lcid.
    lcst1. apply/Hd. 
    apply:factor_seq_r_l. 
    lct2. lct2. lcst1. apply: Hd'. apply: star_o_r.
    rewrite {1}/o /=.
    lct1. lcp1. lcid. lcs1. lcid. apply: star_o_l. eauto.  
Qed.



Lemma derive_unfold_coerce_l : forall c,  dsl (PTree.empty _) c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)). 
Proof.
intros. destruct (derive_unfold_coerce c). done.
Qed.
(*Lemma derive_unfold_coerce_l : forall c R, c_ineq R c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) (proj_sig (derive_unfold_coerce_l_aux c)). 
Proof. intros. apply/c_ineq_gen_mon. pp. done.
Qed.*)

Lemma derive_unfold_coerce_r : forall c, dsl (PTree.empty _) (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c.
Proof.
intros. destruct (derive_unfold_coerce c). done.
Qed.


(*Lemma derive_unfold_coerce_r : forall R c, c_ineq R (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c (proj_sig (derive_unfold_coerce_r_aux c)).
Proof. intros. apply/c_ineq_gen_mon. pp. done.
Qed.*)

(*Definition decomp_l c := proj_sig (derive_unfold_coerce_l_aux c).
Definition decomp_r c := proj_sig (derive_unfold_coerce_r_aux c).*)

(*Lemma decomp_l : forall c, INEQ c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) (proj_sig (derive_unfold_coerce_l_aux INEQ c)). 
Proof. intros. pfold. apply:c_ineq_gen_mon. apply:derive_unfold_coerce_l. eauto.
Qed.

Lemma decomp_r : forall c, INEQ (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) c (proj_sig (derive_unfold_coerce_r_aux INEQ c)). 
Proof. intros. pfold. apply:c_ineq_gen_mon. apply:derive_unfold_coerce_r. eauto.
Qed.*)

(*Definition sum_dsl  (F : A -> dsl) := (\big[cplus/cid]_(a : A) (guard (F a))).*)
(*Definition decomp_rec c R := 
cfix (ctrans (decomp_l R) (sum_dsl (fun a => decomp_rec (a \ c) R)))*)

(*Lemma big_shape: forall c, \big[Plus/Empt]_a (Event a _;_ a \ c) = \big[Plus/Empt]_(i <- map (fun a => (a,a\c)) (index_enum A)) (Event i.1 _;_  i.2).
Proof.
move=> c. move Heq: (index_enum _)=>ef. clear Heq.
elim: ef. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons /=. f_equal. done.
Qed.*)

(*Lemma nu_imp_coerce_aux : forall r0 r1 r2 r3 d R, (nu r0 -> nu r1) -> r2 <⟨R⟩= r3 d ->  ' | o (r0) _+_ r2 <⟨R⟩= o(r1) _+_ r3 d'}.
Proof.
intros. destruct (nu r0) eqn:Heqn. rewrite /o Heqn H //. econ. lcp1. lcid. eauto.
rewrite /o Heqn.
destruct (nu r1). econ. 
lct1. apply:untagL. lct2. apply:retag. eauto.
econ. 
lct1. apply:untagL. lct2. apply:retag. eauto.
Qed.

Lemma nu_imp_coerce : forall r0 r1 r2 r3 d R (H : (nu r0 -> nu r1)) (H' : r2 <⟨R⟩= r3 d),  o (r0) _+_ r2 <⟨R⟩= o(r1) _+_ r3 (proj_sig (nu_imp_coerce_aux r0 r1 H H')).
Proof. pp. Qed.*)

Lemma nu_imp_coerce_aux : forall r0 r1, (nu r0 -> nu r1) ->  o r0 <⟨PTree.empty _⟩= o r1. 
Proof.
intros. destruct (nu r0) eqn:Heqn. rewrite /o Heqn H //. econ. lcid. 
rewrite /o Heqn.
destruct (nu r1). econ.
lct2. apply:untagL.
apply:tagL.
eauto. done.
Qed.

(*Lemma nu_imp_coerce : forall r0 r1 (H : nu r0 -> nu r1),  o r0 <⟨PTree.empty _⟩= o r1 ( proj_sig (nu_imp_coerce_aux r0 r1 H)). 
Proof. pp. Qed.*)


(*Lemma nu_imp_coerce : forall r0 r1 r2 r3 d R (H : (nu r0 -> nu r1)) (H' : r2 <⟨R⟩= r3 d),  o (r0) _+_ r2 <⟨R⟩= o(r1) _+_ r3 (proj_sig (nu_imp_coerce_aux r0 r1 H H')).
Proof. pp. Qed.*)
Lemma big_plus_coerce : forall (l : seq A) F0 F1 R, (forall a, a \in l ->  { n | PTree.get n  R = Some (F0 a,F1 a)}) ->
 (\big[Plus/Empt]_(a <- l) (Event a _;_ F0 a)) <⟨R⟩=  (\big[Plus/Empt]_(a <- l) (Event a _;_ F1 a)).  
Proof.
elim;ssa. rewrite !big_nil. eauto.
rewrite !big_cons. lcp1.  
have: a \in a::l. done. move/X0. case. 
ssa. apply:dsl_var. eauto.
eauto. 
Qed.






(*Inductive contains2_gen bisim : regex -> regex -> Prop :=
 contains2_con c0 c1 (H0: Forall (fun e => bisim (e \ c0) (e \ c1)) (index_enum A)) (H1: nu c0 -> nu c1) : contains2_gen bisim c0 c1.


Lemma contains2_gen_mon: monotone2 contains2_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. 
elim: H0;ssa. inv IN.
Qed.
Hint Resolve contains2_gen_mon : paco.*)



(*Definition Contains2 r0 r1 := paco2 contains2_gen bot2 r0 r1.

Lemma Contains2_der : forall c0 c1, Contains c0 c1 -> Forall (fun e => Contains2 (e \ c0) (e \ c1)) (index_enum A).
Proof.
intros. punfold H.  inv H. 
clear H. elim:H0;ssa. con. inv H.  done.
Qed.


Lemma Contains2_nu : forall c0 c1, Contains2 c0 c1 ->  nu ( c0) -> nu ( c1).
Proof.
intros. punfold H.  inv H. eauto. 
Qed.

*)


(*Definition contains c c' := forall s, Match s c -> Match s c'.*)

Lemma contains_derive : forall c c' e, contains c c' -> contains (e \ c) (e \ c').  
Proof.
move => c c' e. rewrite /equiv. move=> HM s. rewrite -!deriveP. apply/HM.
Qed.


Inductive contains_gen bisim : regex -> regex -> Prop :=
 contains_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: nu c0 -> nu c1) : contains_gen bisim c0 c1.



Definition Contains c0 c1 := paco2 contains_gen bot2 c0 c1.
Hint Unfold  Contains : core.

Lemma contains_gen_mon: monotone2 contains_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve contains_gen_mon : paco.


Theorem contains1 : forall c0 c1, contains c0 c1 -> Contains c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  apply/contains_derive=>//.
- move=>Hnu. have: Match nil c0. apply/Match_nil_nu=>//.
  move/H0. move/nuP=>//. 
Qed.



Theorem contains2 : forall c0 c1, Contains c0 c1 -> contains c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC Hnu HC'. apply/nuP/Hnu/nuP=>//.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.


Theorem containsP : forall c0 c1, contains c0 c1 <-> Contains c0 c1.
Proof.
move=> c0 c1. con. apply/contains1. apply/contains2.
Qed.




Hint Resolve undup_uniq.
Unset Implicit Arguments.

(*Less effecient, fix this later*)
Equations containsb (pp : pder * pder) (visited : seq (pder * pder) ) : bool by wf (r_measure visited pp) := 
 containsb pp visited  with (dec (pp \in visited)) => {
  containsb _  _ (in_left) := true;
  containsb pp visited (in_right) with (dec (uniq_pair pp)) => { 
        containsb pp visited _ (in_left) := ((has nu pp.1) ==> (has nu pp.2)) && 
                                        (foldInAll (index_enum A) (fun e _ => containsb (pair_pd_l e (pp)) (pp::visited)));
        containsb pp visited _ (in_right) := false }
 }.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.

(*Effecient but awkard for proofs*)
Equations containsb2 (pp : pder * pder) (visited : seq (pder * pder) ) (H : uniq_pair pp) : bool by wf (r_measure visited pp) := 
 containsb2 pp visited H  with (dec (pp \in visited)) => {
  containsb2 _  _ _ (in_left) := true;
  containsb2 pp visited _ (in_right) := ((has nu pp.1) ==> (has nu pp.2)) && 
                                           (foldInAll (index_enum A) (fun e _ => containsb2 (pair_pd_l e pp) (pp::visited) _));
 }.
Next Obligation. 
apply/andP.
con. simpl. rewrite /pd_l. done.  simpl. rewrite /pd_l. done.
Defined.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.
Set Implicit Arguments.

Lemma containsb12 : forall pp visited (H : uniq_pair pp), containsb pp visited -> containsb2 pp visited H.
Proof.
intros. funelim (containsb pp visited).
simp containsb2. simpl. rewrite Heq. simpl. done.
simp containsb2. rewrite Heq0. simpl.
rewrite -Heqcall in H1. ssa.
rewrite !foldInAllP in H3 *. 
apply/allP. intro. intros. move: (allP H3 _ H1). move/H. move/inP: H1=>H1'. move/(_ H1')=>Hall.
apply Hall. rewrite -Heqcall in H0. done.
Qed.

Lemma containsb21 : forall pp visited (H : uniq_pair pp), containsb2 pp visited H -> containsb pp visited.
Proof.
intros. funelim (containsb pp visited). rewrite -Heqcall. done.
rewrite -Heqcall. simp containsb2 in H1. rewrite Heq0 in H1. ssa.
rewrite !foldInAllP in H3 *. 
apply/allP. intro. intros. move: (allP H3 _ H1). move/H. move/inP: H1=>H1'. move/(_ H1')=>Hall.
apply Hall.  clear H0.
rewrite e1 in H. done.
Qed.

Lemma containsb_iff : forall pp visited (H : uniq_pair pp), containsb pp visited <-> containsb2 pp visited H.
Proof.
intros. split. apply:containsb12. apply:containsb21.
Qed.

Inductive contains_ind_gen contains : pder -> pder-> Prop :=
 contains_con3 l0 l1 (H0: forall e, contains (pd_l e l0) (pd_l e l1) : Prop ) (H1: has nu l0 -> has nu l1) : contains_ind_gen contains l0 l1.

Definition ContainsInd l0 l1 := paco2 contains_ind_gen bot2 l0 l1.
Hint Unfold  ContainsInd : core.

Lemma contains_ind_gen_mon: monotone2 contains_ind_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve contains_ind_gen_mon : paco.

Lemma containsb_complete_aux : forall l0 l1 l_v, uniq_pair (l0,l1) ->  ContainsInd l0 l1 ->  containsb  (l0,l1) l_v. 
Proof. 
intros. funelim (containsb  (l0,l1) l_v).  rewrite -Heqcall. ssa.
rewrite -Heqcall. ssa. 
punfold H1.  inv H1. apply/eqP=>//. apply/eqP. apply/implyP. done.
rewrite foldInAllP. apply/allP=> x xIn. 
apply:H. apply/inP. eauto.  simpl. 
rewrite /uniq_pair /pd_l. ssa.
punfold H1. inv H1. case: (H2 x)=>//. con. 
done. rewrite  e1 in H. done.
Qed.


Definition containsb_wrap (l l' : pder) := containsb (undup l,undup l') nil.

Theorem equiv_rInd2 : forall l l', ContainsInd l l' -> contains ( (\big[Plus/Empt]_(i <- l) i))  (\big[Plus/Empt]_(i <- l') i).
Proof.
move=> l0 l1 HC s. 
elim: s l0 l1  HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. intros. apply/Match_has_nu_iff/HC'/Match_has_nu_iff.  done.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. 
  rewrite !deriveP2. rewrite /pd_sum. rewrite !pd_plus //.
  apply/IH=>//. 
Qed.

Lemma derive_pd_l2 : forall l e, contains (e \ \big[Plus/Empt]_(i <- l) i) 
                                   (\big[Plus/Empt]_(i <- pd_l e l) i).
Proof.
intros. intro.  move: (derive_pd_l l e s). case. ssa.
Qed.

Lemma derive_pd_l3 : forall l e, contains  (\big[Plus/Empt]_(i <- pd_l e l) i)  (e \ \big[Plus/Empt]_(i <- l) i) .
Proof.
intros. intro.  move: (derive_pd_l l e s). case. ssa.
Qed.

Lemma contains_r_trans : forall r0 r1 r2, contains r0 r1 -> contains r1 r2 -> contains r0 r2.
Proof.
intros. intro. eauto. 
Qed.

Theorem Contains_co_ind : forall l l', Contains (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i) -> ContainsInd l l'.
Proof.
pcofix CIH. intros. punfold H0. inv H0. pfold. con. intros.
right. apply/CIH. 
destruct (H1 e)=>//. apply/containsP. move/containsP : H.
intros. 
apply/contains_r_trans.
apply:derive_pd_l3.
apply/contains_r_trans.
2: { apply:derive_pd_l2. } done.
rewrite !nu_has in H2. done.
Qed.

Lemma Contains_contains : forall l l', ContainsInd l l' <-> contains (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i). 
Proof.
intros. split. apply/equiv_rInd2. move/containsP/Contains_co_ind=>//.
Qed.

Lemma containsb_complete : forall l0 l1, ContainsInd l0 l1 ->  containsb_wrap l0 l1.
Proof.
intros. apply:containsb_complete_aux. rewrite /uniq_pair. ssa. 
apply/Contains_contains.
intro. rewrite !Match_big_undup. move: s. apply/Contains_contains=>//.
Qed.




Lemma c_eq_undup1 : forall l L,  \big[Plus/Empt]_(i <- (undup l)) i <⟨L⟩=  \big[Plus/Empt]_(i <- l) i.
Proof.
elim;ssa.
case_if.  rewrite !big_cons. 
lct2. lcp1. lcid. apply:X. clear X.
elim: l a H;ssa. 
rewrite !inE in H. destruct (eqVneq a0 a).   subst. ssa.

case_if. eauto. rewrite /= !big_cons.
apply:ctrans2. apply:ctrans2. apply:shuffle. lcp1. apply:tagL. lcid.  
lcp1. done. done.
ssa.
case_if=>//. lct2. apply:retag. eauto.
rewrite !big_cons. lct2. apply:retag. eauto.
rewrite !big_cons. eauto.
Qed.

(*Lemma c_eq_undup2 : forall l L, \big[Plus/Empt]_(i <- l) i  <⟨L⟩=  \big[Plus/Empt]_(i <- (undup l)) i.  
Proof.
elim;ssa.
case_if.  rewrite H. rewrite !big_cons. clear H.
elim: l a H0;ssa. 
rewrite !inE in H0. de (orP H0). norm_eqs. rewrite !big_cons. 
apply:c2_trans. 2: { apply:c2_trans.  2: { apply:c2_plus_assoc. }  apply:c2_plus_ctx. apply:c2_sym. apply:c2_plus_idemp. apply:c2_refl. } 
apply:c2_plus_ctx. done. done. rewrite !big_cons.
rewrite -c2_plus_assoc.
rewrite [a0 _+_ a] c2_plus_comm.
rewrite c2_plus_assoc. rewrite -(H a0) //. 
rewrite !big_cons.
apply:c2_plus_ctx. done. done.
Qed.*)

Lemma c_eq_cat1 : forall l0 l1 L,  \big[Plus/Empt]_(i <- l0 ++ l1) i <⟨L⟩=  \big[Plus/Empt]_(i <- l0) i _+_  \big[Plus/Empt]_(i <- l1) i.
Proof.
elim;ssa.
rewrite !big_nil //. 
rewrite !big_cons. lct2.  apply:shuffleinv. lcp1. done.  done.
Qed.

Lemma c_eq_cat2 : forall l0 l1 L,  \big[Plus/Empt]_(i <- l0) i _+_  \big[Plus/Empt]_(i <- l1) i <⟨L⟩=   \big[Plus/Empt]_(i <- l0 ++ l1) i . 
Proof.
elim;ssa.
rewrite !big_nil //. 
rewrite !big_cons. lct1.  apply:shuffle. lcp1. done.  done.
Qed.



Lemma c_eq_derive_pd_l1 : forall c L a, a \ c <⟨ L ⟩ = \big[Plus/Empt]_(i <- pd a c) i.
Proof.
elim;ssa; try solve [ rewrite !big_nil //=].
case_if. norm_eqs. rewrite eqxx //= !big_cons big_nil.  auto.
rewrite eq_sym H big_nil //=.
lct2. apply:c_eq_cat2.
lcp1. done. done.
case_if. lct2. apply:c_eq_cat2. lcp1. rewrite map_big_plus.
lct2. apply:factor_seq_r_r. apply:cseq. done. done. done.
rewrite map_big_plus.
lct2. apply:factor_seq_r_r. apply:cseq. done. done. 
rewrite map_big_plus.
lct2. apply:factor_seq_r_r. apply:cseq. done. done. 
Qed.

Lemma c_eq_derive_pd_l2 : forall c L a, \big[Plus/Empt]_(i <- pd a c) i <⟨ L ⟩ =  a \ c.
Proof. Admitted.

Lemma dsl_mon : forall T0 T1 r0 r1, dsl T0 r0 r1 -> (forall p v, PTree.get p T0 = Some v -> PTree.get p T1 = Some v) -> dsl T1 r0 r1.
Proof.
move=> T0 T1 r0 r1 d.
elim: d T1;auto.
intros. apply:ctrans. apply X. eauto. apply X0. eauto.
intros. apply:dsl_var. eauto.
intros.
have: forall (p : positive), PTree.get p T1 = None -> PTree.get p R = None.
intros. destruct (PTree.get p R) eqn:Heqn. apply H in Heqn. rewrite Heqn in H0. done. done.
move=>Hnone.
apply:dsl_fix. apply:Hnone.


Lemma decomp_p1 : forall l L,  \big[Plus/Empt]_(i <- l) i <⟨L⟩= (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i ). 
Proof. 
intros.  
lct1. 
Check derive_unfold_coerce_l.
apply:derive_unfold_coerce_r.
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

Lemma decomp_p2 : forall l L,  (o_l l) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ \big[Plus/Empt]_(i <- pd_l a l) i )  <⟨L⟩=.  \big[Plus/Empt]_(i <- l) i 

Definition is_sub {A: eqType} (l0 l1 : seq A) := forall x, x \in l0 -> x \in l1.
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

Definition plusV (V : seq (pder * pder)) := map (fun x => (\big[Plus/Empt]_(i <- x.1) i,(\big[Plus/Empt]_(i <- x.2) i))) V.
Lemma EQ_complete_aux : forall l l' V L, uniq_pair (l,l') ->
    (forall x y, (x,y) \in V ->  (\big[Plus/Empt]_(i <- x) i, \big[Plus/Empt]_(i <- y) i) \in L) -> 
                                                         bisim (l,l') V -> 
                                                         ((\big[Plus/Empt]_(i <- l) i), (\big[Plus/Empt]_(i <- l') i)) \in L \/
                                                         (\big[Plus/Empt]_(i <- l) i) =⟨L⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. move: L H0. simpl. funelim (bisim (l,l') V). eauto.
intros.
right. apply c2_fix.
ssa.  rewrite -Heqcall in H1. ssa. 
rewrite foldInAllP in H4. 
apply:c2_trans. apply:decomp_p. 
apply:c2_trans. 2: {  apply:c2_sym. apply:decomp_p. } 
apply:c2_plus_ctx. apply:(@c_eq_mon _ _ nil)=>//. apply:o_lP.  apply/eqP. done.
clear Heqcall Heq. clear e0 Heq0 H3. rewrite /pair_pd_l in H. simpl in H. clear e H0.
move  HeqL':  ((\big[Plus/Empt]_(i <- l) i, \big[Plus/Empt]_(i <- l') i) :: L) => L'.
suff: forall a, Event a _;_  \big[Plus/Empt]_(i <- pd_l a l) i =⟨L'⟩= Event a _;_  \big[Plus/Empt]_(i <- pd_l a l') i.
intros. clear H H2 H4 HeqL'.
move: H0.
move:(index_enum A)=> lA.
elim: lA. 
ssa. rewrite !big_nil. done.
ssa. rewrite !big_cons. apply:c2_plus_ctx. done. 
apply/H. done.
intros.
move Heq : ( \big[Plus/Empt]_(i <- pd_l a l) i) => r0.
move Heq2 : ( \big[Plus/Empt]_(i <- pd_l a l') i) => r1.
suff:    
(r0,r1) \in L'

\/
 r0 =
  ⟨L'⟩ =
   r1.
intros. destruct H0. apply:c2_var. done. 
apply:c2_seq_ctx. done. done.
subst. apply:H. 
4: { con. }  
apply/inP. done.
rewrite /uniq_pair /pd_l //; ssa; apply:undup_uniq. 
apply (allP H4). done. done.
intros. 
rewrite !inE in H. de (orP H). norm_eqs. inv H0. rewrite eqxx //. auto.
rewrite -Heqcall in H1. ssa.
Qed.

Lemma bisim_c_eq : forall l l', bisim_wrap l l' ->  (\big[Plus/Empt]_(i <- l) i) =⟨nil⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. eapply (@EQ_complete_aux _ _ _ nil) in H. destruct H. done. 
rewrite !c_eq_undup in H. done. rewrite /uniq_pair //=;ssa;apply:undup_uniq.
ssa.
Qed.


Theorem Bisim_to_sum : forall c0 c1, Bisimilarity c0 c1 -> Bisimilarity (\big[Plus/Empt]_(i <- c0::nil) i) (\big[Plus/Empt]_(i <- c1::nil) i). 
Proof.
intros. apply:equiv_r1. rewrite !big_cons !big_nil.
suff : equiv_r c0 c1. intro. intro. split. intros. inv H1;ssa. 
con. apply/H0. done. intros. inv H1. con. apply/H0. done.
inv H4. 
apply:equiv_r2. done.
Qed.


Lemma c_eq_coind_ind: forall c0 c1, EQ c0 c1 ->  c0 =⟨nil⟩= c1.
Proof.
intros. 
move/bisim_soundness:H. move/Bisim_to_sum.
move/Bisim_co_ind. 
move/bisim_complete. 
move/bisim_c_eq. rewrite !big_cons !big_nil. eauto.
Qed.




End DecideBismim.

Section Equivalence_Completeness.

Definition o_l l := if has nu l then Eps else Empt.

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

Definition is_sub {A: eqType} (l0 l1 : seq A) := forall x, x \in l0 -> x \in l1.
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

Definition plusV (V : seq (pder * pder)) := map (fun x => (\big[Plus/Empt]_(i <- x.1) i,(\big[Plus/Empt]_(i <- x.2) i))) V.
Lemma EQ_complete_aux : forall l l' V L, uniq_pair (l,l') ->
    (forall x y, (x,y) \in V ->  (\big[Plus/Empt]_(i <- x) i, \big[Plus/Empt]_(i <- y) i) \in L) -> 
                                                         bisim (l,l') V -> 
                                                         ((\big[Plus/Empt]_(i <- l) i), (\big[Plus/Empt]_(i <- l') i)) \in L \/
                                                         (\big[Plus/Empt]_(i <- l) i) =⟨L⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. move: L H0. simpl. funelim (bisim (l,l') V). eauto.
intros.
right. apply c2_fix.
ssa.  rewrite -Heqcall in H1. ssa. 
rewrite foldInAllP in H4. 
apply:c2_trans. apply:decomp_p. 
apply:c2_trans. 2: {  apply:c2_sym. apply:decomp_p. } 
apply:c2_plus_ctx. apply:(@c_eq_mon _ _ nil)=>//. apply:o_lP.  apply/eqP. done.
clear Heqcall Heq. clear e0 Heq0 H3. rewrite /pair_pd_l in H. simpl in H. clear e H0.
move  HeqL':  ((\big[Plus/Empt]_(i <- l) i, \big[Plus/Empt]_(i <- l') i) :: L) => L'.
suff: forall a, Event a _;_  \big[Plus/Empt]_(i <- pd_l a l) i =⟨L'⟩= Event a _;_  \big[Plus/Empt]_(i <- pd_l a l') i.
intros. clear H H2 H4 HeqL'.
move: H0.
move:(index_enum A)=> lA.
elim: lA. 
ssa. rewrite !big_nil. done.
ssa. rewrite !big_cons. apply:c2_plus_ctx. done. 
apply/H. done.
intros.
move Heq : ( \big[Plus/Empt]_(i <- pd_l a l) i) => r0.
move Heq2 : ( \big[Plus/Empt]_(i <- pd_l a l') i) => r1.
suff:    
(r0,r1) \in L'

\/
 r0 =
  ⟨L'⟩ =
   r1.
intros. destruct H0. apply:c2_var. done. 
apply:c2_seq_ctx. done. done.
subst. apply:H. 
4: { con. }  
apply/inP. done.
rewrite /uniq_pair /pd_l //; ssa; apply:undup_uniq. 
apply (allP H4). done. done.
intros. 
rewrite !inE in H. de (orP H). norm_eqs. inv H0. rewrite eqxx //. auto.
rewrite -Heqcall in H1. ssa.
Qed.

Lemma bisim_c_eq : forall l l', bisim_wrap l l' ->  (\big[Plus/Empt]_(i <- l) i) =⟨nil⟩= (\big[Plus/Empt]_(i <- l') i).
Proof.
intros. eapply (@EQ_complete_aux _ _ _ nil) in H. destruct H. done. 
rewrite !c_eq_undup in H. done. rewrite /uniq_pair //=;ssa;apply:undup_uniq.
ssa.
Qed.


Theorem Bisim_to_sum : forall c0 c1, Bisimilarity c0 c1 -> Bisimilarity (\big[Plus/Empt]_(i <- c0::nil) i) (\big[Plus/Empt]_(i <- c1::nil) i). 
Proof.
intros. apply:equiv_r1. rewrite !big_cons !big_nil.
suff : equiv_r c0 c1. intro. intro. split. intros. inv H1;ssa. 
con. apply/H0. done. intros. inv H1. con. apply/H0. done.
inv H4. 
apply:equiv_r2. done.
Qed.

















































Lemma Contains_coerce : forall r0 r1, Contains r0 r1 -> dsl_co r0 r1.
Proof.
cofix CIH.
intros. con.
move: (Contains_der H) (Contains_nu H)=>Hder Hnu. 
apply:ctrans. apply:(antim_l).
apply:ctrans. 2: apply:(antim_r). 
apply:cplus. apply:nu_coerce. done. 
clear Hnu.
apply:guard. intros. apply:CIH. apply:Hder.
Qed.
(*Check guard.
Check guard.
Check (guard dsl_co).
eapply guard.
cofix CIH2.
move: Hder. move:(index_enum A)=> l.

elim:Hder. rewrite !big_nil. con.
intros. rewrite !big_cons. apply:cplus. 
apply:guard. apply:CIH. apply:H0. 
apply:CIH.

(*move: (index_enum _) => l.
elim: l.
rewrite !big_nil. con.
intros. rewrite !big_cons. *)
(*apply:cplus. 2:eauto. *)
apply:guard. apply:CIH. eauto. apply:Hder.
Qed.

intros.
punfold H. destruct H.*)































(* (derive_unfold_coerce_l_aux  
   Must be called with bot3, instead of (upaco3 c_ineq r)
   Because r was not in the context when ?d was introduced
  *)

Lemma coerce_complete : forall c0 c1, Contains c0 c1 -> exists d, INEQ c0 c1 d.
Proof.
move=> c0 c1. econ.
move: c0 c1 H.
pcofix CIH.
intros. punfold H0. inversion H0. subst. pfold. 
lct1. apply:derive_unfold_coerce_l.
lct2. apply:derive_unfold_coerce_r. apply: nu_imp_coerce. done.
apply: big_plus_coerce. intros. right. apply/CIH.  case: (H1 a)=>//.
simpl.
 
simpl. 

instantiate (1:=
 ctrans (proj_sig (derive_unfold_coerce_l_aux (upaco3 c_ineq bot3) c0)) 
    (ctrans
       (proj_sig
          (nu_imp_coerce_aux c0 c1 H2
             (big_plus_coerce (index_enum A) (derive^~ c0) (derive^~ c1) (fun=> shuffle) 
                (upaco3 c_ineq bot3)
                (fun a : A =>
                 fun=> or_intror
                         (CIH (a \ c0) (a \ c1)
                            match H1 a with
                            | or_introl a0 => a0
                            | or_intror b => False_ind (Contains (a \ c0) (a \ c1)) b
                            end))))) (proj_sig (derive_unfold_coerce_r_aux (upaco3 c_ineq bot3) c1)))).

instantiate (1:= shuffle).

(*instantiate (1:= cfix (var_dsl 0)).*)
instantiate (1 := (
(ctrans (proj_sig (derive_unfold_coerce_l_aux (upaco3 c_ineq bot3) c0)) cid))).
    (ctrans cid cid)))).
       (proj_sig   
          (nu_imp_coerce_aux c0 c1 H2
             (big_plus_coerce (index_enum A) (derive^~ c0) (derive^~ c1) (fun=> guard (var_dsl 0) )
                (upaco3 c_ineq r)
                (fun a : A =>
                 fun=> or_intror
                         (CIH (a \ c0) (a \ c1)
                            match H1 a with
                            | or_introl a0 => a0
                            | or_intror b => False_ind (Contains (a \ c0) (a \ c1)) b
                            end))))) (proj_sig (derive_unfold_coerce_r_aux (upaco3 c_ineq r) c1)))))).

 instantiate (1:= shuffle). simpl.

t0.
rewrite !big_shape.

rewrite (derive_unfold _ c0) (derive_unfold _ c1). subst.
rewrite /o H2.
suff:    \big[Plus/Empt]_a (Event a _;_ a \ c0) = (upaco2 c_eqc r)=
  \big[Plus/Empt]_a (Event a _;_ a \ c1). move=> HH.
 case Hcase:(nu _)=>//. eq_m_left. eq_m_left.
rewrite !big_shape.
move: (index_enum _)=>ef. elim: ef=>//.
move=> a l HQ/=. rewrite !big_cons. apply/c_plus_ctx=>//.
apply/c_fix=>/=. right. apply/CIH. case: (H1 a)=>//.
Qed.



(*Lemma big_shape: forall c, \big[Plus/Empt]_a (Event a _;_ a \ c) = \big[Plus/Empt]_(i <- map (fun a => (a,a\c)) (index_enum A)) (Event i.1 _;_  i.2).
Proof.
move=> c. move Heq: (index_enum _)=>ef. clear Heq.
elim: ef. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons /=. f_equal. done.
Qed.*)

Lemma contains_equiv : forall c0 c1, contains c0 c1 -> equiv (c0 _+_ c1) c1.
Proof.
intros. intro. split. intros. inv H0. eauto. eauto.
Qed.

Lemma contains_EQ : forall c0 c1, contains c0 c1 -> EQ  (c0 _+_ c1) c1.
Proof.
move=> c0 c1 /contains_equiv /completeness=>//.
Qed.


































Section CoinductiveDSL.
Inductive dsl (R: regex -> regex -> Type) : regex -> regex -> Type := 
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
(*| cfix r r' (p  : dsl R dsl) : dsl R r  r' p[d (cfix p) .: dsl R var_dsl] ->  r  r' (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dsl R ((Event a) _;_ A)  ((Event a) _;_ B)*)
| guard (F F' : A -> regex)  : (forall a, R (F a) (F' a)) -> dsl R (\big[Plus/Empt]_(a: A) ((Event a) _;_ F a))
                                                          (\big[Plus/Empt]_(a: A) ((Event a) _;_ F' a)).
(**)

CoInductive dsl_co : regex -> regex -> Type := 
| Co_build A B : (dsl dsl_co) A B -> dsl_co A B.


End DSL.
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
(*Arguments guard {R a A B}.*)

(*Arguments Co_build {A B}.*)









Lemma nu_coerce : forall r0 r1 (H: nu r0 -> nu r1), dsl dsl_co (o r0) (o r1).
Proof.
intros.
rewrite /o. destruct (nu _)eqn:Heqn. rewrite H. con. done.
destruct (nu r1) eqn:Heq. apply:ctrans. 2: apply:untagL. apply:tagL.
con.
Qed.

Lemma antim_l : forall r, dsl dsl_co r ((o r) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ r)).
Proof. Admitted.

Lemma antim_r : forall r, dsl dsl_co ((o r) _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ r)) r.
Proof. Admitted.

Lemma antim_l2 : forall r a, dsl dsl_co r ((o r) _+_ (Event a _;_ a \ r)).
Proof. Admitted.

Lemma antim_r2 : forall r a, dsl dsl_co ((o r) _+_ (Event a _;_ a \ r)) r.
Proof. Admitted.



CoFixpoint co_test :=  Co_build (ctrans shuffle (guard co_test)).


CoFixpoint produce_dsl R r0 r1 (H: bisimilarity_gen R r0 r1) := 












End Regex.
