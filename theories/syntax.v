From HB Require Import structures.


From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
Require Import ConstructiveEpsilon.

From Containment Require Import  utils dsl dsl_theory.
Set Implicit Arguments.
Set Maximal Implicit Insertion.


Let inE := utils.inE.

Section Regex.
Variable A : finType. (**)
(*Variable (As : Set).
Hypothesis (H : Finite.axioms_ As).
Definition A : finType := @Finite.Pack As H.
Check @Finite.Pack.
Check (Finite.sort A).
Check A.*)
Definition trace := seq A.

Check nat_rect.


Inductive regex : Type :=
| Eps : regex
| Empt : regex
| Event : A -> regex
| Plus : regex -> regex -> regex
| Seq : regex -> regex -> regex
| Star : regex -> regex.

Notation "c0 _;_ c1"  := (Seq c0 c1)
                         (at level 52, left associativity).

Notation "c0 _+_ c1"  := (Plus c0 c1)
                         (at level 53, left associativity).

(*Inductive pTree : regex -> Type := 
| p_tt : pTree Eps 
| p_singl a : pTree (Event a)
| p_inl {r0 r1} : pTree r0 -> pTree (r0 _+_ r1) 
| p_inr r0 r1 : pTree r1 -> pTree (r0 _+_ r1) 
| p_pair r0 r1 : pTree r0 -> pTree r1 -> pTree (r0 _;_ r1)
| p_fold r : pTree (Eps _+_ (r _;_ (Star r))) -> pTree (Star r).
End Regex.
*)


(*Notation "e _._ c" := (Seq (Event e) c)
                    (at level 51, right associativity).*)



Definition regex_indDef := [indDef for regex_rect].
Canonical regex_indType := IndType regex regex_indDef.

Definition regex_hasDecEq := [derive hasDecEq for regex].
HB.instance Definition _ := regex_hasDecEq.


Fixpoint nu(c:regex ):bool :=
match c with
| Eps => true
| Empt => false
| Event e => false
| Seq c0 c1 => nu c0 && nu c1
| Plus c0 c1 => nu c0 || nu c1
| Star c => true
end.

Reserved Notation "e \ c" (at level 40, left associativity).

Fixpoint derive (e:A) (c:regex) :regex :=
match c with
| Eps => Empt
| Empt => Empt
| Event e' => if e' == e then Eps else Empt
| c0 _;_ c1 => if nu c0 then
                 ((e \ c0) _;_ c1) _+_ (e \ c1)
                 else (e \ c0) _;_ c1
| c0 _+_ c1 => e \ c0 _+_ e \ c1
| Star c => e \ c _;_ (Star c)
end
where "e \ c" := (derive e c).


Ltac destruct_ctx :=
  repeat match goal with
         | [ H: ?H0 /\ ?H1 |- _ ] => destruct H
         | [ H: exists _, _  |- _ ] => destruct H
         end.



Ltac autoIC := auto with cDB.

Reserved Notation "s \\ c" (at level 42, no associativity).
Fixpoint trace_derive (s : trace) (c : regex)  : regex :=
match s with
| [::] => c
| e::s' => s' \\ (e \ c)
end
where "s \\ c" := (trace_derive s c).


(*Reserved Notation "s (:) re" (at level 63).*)
Inductive Match : trace -> regex -> Prop :=
  | MEps : Match [::]  Eps
  | MEvent x : Match [::x] (Event x)
  | MSeq s1 c1 s2 c2 :
             Match s1 c1 ->
             Match s2 c2 ->
             Match (s1 ++ s2) (c1 _;_ c2)
  | MPlusL s1 c1 c2:
               Match s1 c1 ->
               Match s1 (c1 _+_ c2)
  | MPlusR c1 s2 c2:
               Match s2 c2 ->
               Match s2 (c1 _+_ c2)
  | MStar0 c  : Match [::] (Star c)
  | MStarSeq c s1 s2:
                Match s1 c ->
                Match s2 (Star c) ->
                Match (s1 ++ s2) (Star c).
Hint Constructors Match.


Lemma MSeq2: forall s0 s1 c0 c1 s, Match s0 c0 -> Match s1 c1 -> s = s0 ++ s1  -> Match s (c0 _;_ c1).
Proof.
move => s0 s1 c0 c1 s HM0 HM1 Heq;subst. eauto.
Qed.

Lemma MStar2 : forall s0 s1 c s, Match s0 c -> Match s1 (Star c) -> s = s0 ++ s1  -> Match s (Star c).
Proof.
move => s0 s1 c s HM0 HM1 Heq;subst. eauto.
Qed.

Definition equiv (r0 r1: regex) := forall s, Match s r0 <-> Match s r1.

Lemma seq_Eps : forall c, equiv (Eps _;_ c) c.
Proof.
move=> c s;split;intros. inversion H. inversion H3; subst. now simpl. by  apply/MSeq2;eauto.
Qed. 

Lemma seq_Empt : forall c, equiv (Empt _;_ c) Empt.
Proof.
move=> c s;split;intros. inversion H. inversion H3. inversion H.
Qed.

Hint Resolve seq_Eps seq_Empt.


Lemma derive_distr_plus : forall (s : trace)(c0 c1 : regex), s \\ (c0 _+_ c1) = s \\ c0 _+_ s \\ c1.
Proof.
induction s;intros;simpl;auto.
Qed. 

Hint Rewrite derive_distr_plus.

Lemma nu_seq_derive : forall (e : A)(c0 c1 : regex), 
nu c0 -> nu (e \ c1) -> nu (e \ (c0 _;_ c1)).
Proof.
intros. simpl. destruct (nu c0). simpl. auto with bool. discriminate.
Qed.

Lemma nu_Empt : forall (s : trace)(c : regex), nu (s \\ (Empt _;_ c)) = false.
Proof.
induction s;intros. now simpl. simpl. auto.
Qed.

Hint Rewrite nu_Empt.

Lemma nu_Eps : forall (s : trace)(c : regex), nu (s \\ (Eps _;_ c)) = nu (s \\ c).
Proof.
induction s;intros;simpl;auto. 
by rewrite derive_distr_plus /= nu_Empt //=.
Qed.

Lemma nu_seq_trace_derive : forall (s : trace)(c0 c1 : regex), 
nu c0 -> nu (s \\ c1) -> nu (s \\ (c0 _;_ c1)).
Proof.
induction s;intros;simpl in *. intuition. destruct (nu c0).
rewrite derive_distr_plus. simpl. auto with bool. discriminate.
Qed.

Lemma matchb_seq : forall (s0 s1 : trace)(c0 c1 : regex), nu (s0\\c0) 
                                                      -> nu (s1\\c1)-> nu ((s0++s1)\\(c0 _;_c1)).
Proof.
induction s0;intros;simpl in *.
- rewrite nu_seq_trace_derive; auto. 
- destruct (nu c0);first by rewrite derive_distr_plus /= IHs0//.
  rewrite IHs0 //.
Qed.

Definition matchb s r := nu (trace_derive s r).

Lemma Match_i_matchb : forall (c : regex)(s : trace), Match s c -> matchb s c.  
Proof.
move=> c s. rewrite /matchb. elim=>//=.
- move => x. rewrite eqxx//.
- move => s1 c1 s2 c2 HM0 HN0 HM1 HN1/=. by apply/matchb_seq=>//.
- move=> s1 c1 c2 HM HN. rewrite derive_distr_plus /= HN//.
- move=> c1 s2 c2 HM HN. rewrite derive_distr_plus /= HN orbC //.
- move=> c0 []//= a l s2 HM HN HM' HN' /=. by apply/matchb_seq=>//.
Qed.



Lemma Match_nil_nu : forall (c : regex), nu c  -> Match [::] c.
Proof.
intros;induction c; simpl in H ; try discriminate; auto.
- case: (orP H). move/IHc1;eauto. move/IHc2;eauto.
- case: (andP H). move=>/IHc1 HH0 /IHc2 HH1. apply/MSeq2;eauto.
Qed.



Lemma Match_nil_seq: forall c0 c1, Match nil (Seq c0 c1) -> Match nil c0 /\ Match nil c1.
Proof.
move=> c0 c1 HM. inversion HM;subst. 
destruct s1;ssa. destruct s2;ssa.
Qed.

Lemma nuP : forall c, nu c <-> Match [::] c.
Proof.
move=> c. con;first by apply/Match_nil_nu=>//.
elim: c=>//=. move=> HM. inv HM. move=> s HM. inv HM.
move=> r IH r0 HM HM2. apply/orP. inv HM2;eauto.
move=> r IH r0 IH2 HM. apply/andP.
move/Match_nil_seq: HM=>[]. eauto.
Qed.


(*This direction with longer trace on the right because of induction step on trace*)
Lemma Match_matchb : forall (c : regex)(e : A)(s : trace), Match s (e \ c)-> Match (e::s) c.
Proof.
induction c;intros; simpl in*; try solve [inversion H].
- move: H. case Hcase:(_==_)=>// HM. rewrite (eqP Hcase).
  inv HM;auto. inv HM.
- inv H;eauto.
- destruct (nu c1) eqn:Heqn.
  * inv H.
    ** inv H2. apply/MSeq2;eauto.
    ** apply/MSeq2. apply/Match_nil_nu=>//. eauto. done.
  * inv H. apply/MSeq2. eauto. eauto. done.
- inversion H. apply/MStar2;eauto.
Qed.




Theorem  matchbP: forall (c : regex)(s : trace), Match s c <-> matchb s c. 
Proof.
move=> c s. rewrite /matchb.
split;first by apply/Match_i_matchb=>//.
elim: s c=>//;first by move=> c /Match_nil_nu=>//.
move=> a l IH c /=. move/IH/Match_matchb=>//.
Qed.

Lemma deriveP : forall (c : regex)(e : A)(s : trace), Match (e::s) c <-> Match s (e \ c).
Proof.
by move=> c e s; rewrite !matchbP.
Qed.


Section Equivalence.
  Variable co_eq : regex -> regex -> Prop.
Reserved Notation "c0 =R= c1" (at level 63).


(*Maybe c_star_ctx and c_star_plus are not necessary*)

Inductive c_eq : regex -> regex -> Prop :=
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
 where "c1 =R= c2" := (c_eq c1 c2).
End Equivalence.
Hint Constructors c_eq.

Section Equivalence_Properties.

Lemma c_eq_gen_mon: monotone2 c_eq. 
Proof.
unfold monotone2.
intros. induction IN; eauto. 
Qed.
Hint Resolve c_eq_gen_mon : paco.


Notation "c0 = ( R ) = c1" := (c_eq R c0 c1)(at level 63).
Definition EQ c0 c1 := paco2 c_eq bot2 c0 c1.
Notation "c0 =C= c1" := (EQ c0 c1)(at level 63).

Require Import Relation_Definitions Setoid.

Add Parametric Relation R : regex (@c_eq R)
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
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as c_eq_plus_morphism.
Proof.
intros. eauto. 
Qed.

Add Parametric Morphism R : Seq with
signature (c_eq R) ==> (c_eq R) ==> (c_eq R) as co_eq_seq_morphism.
Proof.
intros. eauto.
Qed.

Add Parametric Morphism R : Star with
signature (c_eq R) ==> (c_eq R) as c_eq_star_morphism.
Proof.
intros. eauto.
Qed.

Lemma c_plus_neut_l : forall R c, Empt _+_ c =(R)= c.
Proof. intros. rewrite c_plus_comm. auto.
Qed.


Lemma c_eq_nu : forall R (c0 c1 : regex) , c0 =(R)= c1 -> nu c0 = nu c1.
Proof. 
intros. induction H; simpl; auto with bool; try btauto.
all : try (rewrite IHc_eq1; rewrite IHc_eq2; auto).
(*clear H.
elim: H0=>//. move=> x y l l' R' Hfor IH.
rewrite !big_cons //=.*)
Qed.

Lemma co_eq_nu : forall (c0 c1 : regex) , c0 =C= c1 -> nu c0 = nu c1.
Proof. 
intros. eapply c_eq_nu. punfold H.
Qed.

Lemma plus_empt : forall (A: eqType) R (l : seq A), \big[Plus/Empt]_(a <- l) (Empt) = (R) = Empt.
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

Lemma o_plus : forall c0 c1 R, o (c0 _+_ c1) =(R)= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto. rewrite eqs_aux //.
Qed.

Lemma o_seq : forall c0 c1 R, o (c0 _;_ c1) =(R)= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto.
Qed.

(*Lemma o_true : forall c, nu c = true -> o c = Eps.
Proof.
intros. unfold o. destruct (nu c);auto. discriminate.
Qed. 

Lemma o_false : forall c, nu c = false -> o c = Empt.
Proof.
intros. unfold o. destruct (nu c);auto. discriminate.
Qed. 

Lemma o_destruct : forall c, o c = Eps \/ o c = Empt.
Proof.
intros. unfold o. destruct (nu c);auto || auto.
Qed.*)

(*Makes rewriting non-terminating*)
Lemma seq_comm_o : forall R c c', c _;_ (o c') =(R)= (o c') _;_ c.
Proof.
move=> R c c'. rewrite /o. case Hcase: (nu _)=>//; rewrite !eqs_aux //.
Qed.


Let eqs :=   (eqs_aux,o_plus,o_seq).


(*Lemma c_fix_derive : forall l0 l1 R e,
                                 Forall2 (fun x y => x.1 = y.1) l0 l1 -> Forall2 (fun r0 r1 => r0.2 =(R)= r1.2) l0 l1 ->
                                  e \ \big[Plus/Empt]_(i <- l0) ((Event i.1) _;_ i.2) =(R)= 
                                  e \  \big[Plus/Empt]_(i <- l1) ((Event i.1) _;_ i.2).
Proof.
move=> l0 l1 R e Hfor Hfor'.
elim: Hfor Hfor' e;first by move=> _ e. 

move=> x y l l' Hlab Hfor IH /Forall2_cons [] HR Hfor' e.
rewrite !big_cons /= Hlab. case Hcase:(_==_)=>//.
rewrite !eqs. apply/c_plus_ctx=>//. apply/IH. done.
rewrite !eqs. apply/IH. done.
Qed.*)

Ltac eq_m_left := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto.

Lemma co_eq_derive : forall (c0 c1 : regex) e, c0 =C= c1 -> e \ c0 =C= e \ c1.
Proof.
intros. pfold. punfold H. induction H; try solve [ simpl; rewrite ?eqs;eauto] . 
- rewrite /=. case Hcase: (nu c0)=>//=. case Hcase1: (nu c1)=>//=; rewrite !eqs;eq_m_left. 
- rewrite /=; case Hcase:(nu _)=>//=; rewrite !eqs //.
- rewrite /=; case Hcase: (nu _)=>//;rewrite !eqs //.  
- rewrite /=; case Hcase: (nu _)=>//;rewrite !eqs //. eq_m_left. 
  rewrite c_plus_comm. eq_m_left.
- rewrite /=. case Hcase:(nu c0)=>//=;case Hcase':(nu c1)=>/=//;rewrite !eqs;eq_m_left. 
  rewrite {2}c_plus_comm -c_plus_assoc eqs c_plus_comm //. 
- rewrite /= eqs; case Hcase:(nu _)=>/=;rewrite  ?eqs //. 
- rewrite /=. 
  have: nu c0 = nu c0' by apply/c_eq_nu; eauto. move=>->.
  case Hcase:(nu _)=>//=. eauto.  eauto. 
- rewrite /=. case Hcase: (_==_)=>//. rewrite !eqs //. case: H=>//=>H'. pfold_reverse.
  rewrite !eqs //.
(*econ.
apply c_fix_derive. done. clear H. elim: H0. done. move=> x y l l' [] // HC Hfor Hfor'. con. punfold HC. 
  done.*)
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

Lemma bisim_soundness : forall (c0 c1 : regex), c0 =C= c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. 
intros. pfold. constructor.
- intros. right. apply CIH.  apply co_eq_derive. auto.
- auto using co_eq_nu.
Qed.



(*Let o_eqs := (o_plus,o_seq,o_true,o_false).*)

Definition ex_eq {A : eqType} (l: seq A) (F0 F1 : A -> regex) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus : forall (l : seq A) F1 F2 (R: regex -> regex -> Prop), ex_eq l F1 F2 (c_eq R) ->
   \big[Plus/Empt]_(i <- l) F1 i =( R )= \big[Plus/Empt]_(i <- l) F2 i.
Proof.
move=> + F1 F2 R. 
rewrite /ex_eq. elim=>//.
move=> _. rewrite !big_nil//.
move=> a l IH Hin. rewrite !big_cons. rewrite Hin //. 
eq_m_left.
Qed.

(*Necessary to use ssreflect under for rewriting*)
Add Parametric Morphism R : (Under_rel regex (c_eq R)) with
signature (c_eq R ==> c_eq R ==> flip impl) as under_c_eq. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''. apply/c_trans.  eauto. apply/c_trans. eauto. apply/c_sym. eauto.
Qed.

Add Parametric Morphism R : (Under_rel regex (c_eq R)) with
signature (c_eq R ==> c_eq R ==> impl) as under_c_eq2. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''.  apply/c_trans;last by eauto. apply/c_trans;last by eauto. apply/c_sym. eauto.
Qed.

(*This has to be proved by induction because I cannot use ssreflects big_split since commutativity is over c_eq, and not leibniz equality*)
Lemma split_plus : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) = (R) = \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a).  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil // eqs //.
move=> a l IH. rewrite !big_cons. eq_m_left. rewrite IH. eauto.
Qed.

Lemma factor_seq_l : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (c _;_ P a) =(R)=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)).
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil eqs //.
move=> a l IH. rewrite !big_cons eqs //= IH //.
Qed.



Lemma factor_seq_r : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (P a _;_ c) =(R)= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c.
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil eqs //.
move=> a l IH. rewrite !big_cons eqs //= IH //.
Qed.


Lemma big_event_notin R : forall l a, a \notin l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) =(R)= Empt. 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //.
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite (negbTE Hneq) IH // !eqs //.
Qed.

Lemma big_event_in R : forall l a, a \in l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) =(R)= Event a. 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. move/orP. case. move/eqP=>Heq;subst.
rewrite big_cons eqxx //= !eqs.
case Hcase: (a \in l). rewrite IH. apply/c_plus_idemp=>//. rewrite Hcase//.
rewrite big_event_notin //. rewrite Hcase//.
move=>Hin. rewrite big_cons IH //.
case: (eqVneq a a0). move=>Heq;subst. rewrite !eqs //.
move=>Hneq. rewrite !eqs //=.
Qed.

(*Shorten this proof*)
Lemma derive_seq : forall R a r r', a \ (r _;_ r') =(R)= ((a \ r) _;_ r') _+_ (o (r) _;_ a \ r').
Proof.
move=> R a r r' /=. case Hcase: (nu r)=>/=. rewrite /o Hcase /= eqs //.
rewrite /o Hcase !eqs //.
Qed.



(*Why we need star ctx, 
  Proof below is by induction on regex syntax, to use IH, we need c0 = c1 -> c0* = c1*
  This cannot be derived, as we need some coinductive rule, namely c_fix, which requires
  us to show this decomposition rule to be useful
*)


(*Uses c_star_plus!*)
Lemma star_o : forall R c c', Star (o (c) _+_ c') =(R) = Star c'.
Proof.
move=> R c c'. 
rewrite /o. case Hcase: (nu c);last by rewrite eqs //. clear Hcase.
rewrite c_star_plus //.
Qed.

Lemma derive_unfold : forall R c, c =(R)= o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c). 
Proof.
move=>R. 
elim.
- rewrite /o /=. under eq_big_plus. move=> a Hin. rewrite !eqs. over. rewrite plus_empt eqs //.
- rewrite /o /=. under eq_big_plus. move=> a Hin. rewrite !eqs. over. rewrite plus_empt eqs //.
- move => s. rewrite big_event_in /o //= ?eqs // mem_index_enum //. 
- move=> r HQ r' HQ'. rewrite o_plus /=. 
  under eq_big_plus. move=> a Hin. rewrite eqs. over. 
  rewrite split_plus. 
  apply/c_trans. apply/c_plus_ctx. apply: HQ. apply: HQ'. eq_m_left.  
  rewrite c_plus_comm. eq_m_left.
- move=> r HQ r' HQ'. 
  under eq_big_plus. move=> a Hin. 
  rewrite derive_seq !eqs -!c_seq_assoc seq_comm_o (c_seq_assoc _ (o r)).
  over.
  rewrite split_plus !factor_seq_l !factor_seq_r  o_seq. 
  apply/c_trans. apply/c_seq_ctx. apply: HQ. apply: HQ'.
  apply/c_trans. 2 : {  apply/c_plus_ctx. apply/c_refl. apply/c_plus_ctx. apply/c_seq_ctx. apply/c_refl.
                        apply/c_sym. apply: HQ'. apply/c_refl. }
  rewrite !eqs. eq_m_left. 
- move=> r HQ /=. 
  under eq_big_plus. move=> a Hin. rewrite -c_seq_assoc. rewrite {2}HQ. over.
  rewrite factor_seq_r. rewrite {1}HQ.
  rewrite !star_o /o /= c_unfold //.  (*We need c_star_plus here*)
Qed.

Lemma big_shape: forall c, \big[Plus/Empt]_a (Event a _;_ a \ c) = \big[Plus/Empt]_(i <- map (fun a => (a,a\c)) (index_enum A)) (Event i.1 _;_  i.2).
Proof.
move=> c. move Heq: (index_enum _)=>ef. clear Heq.
elim: ef. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons /=. f_equal. done.
Qed.


Lemma bisim_completeness : forall c0 c1, Bisimilarity c0 c1 -> c0 =C= c1.
Proof.
pcofix CIH.
intros. punfold H0. inversion H0.
pfold. rewrite (derive_unfold _ c0) (derive_unfold _ c1). subst.
rewrite /o H2.
suff:    \big[Plus/Empt]_a (Event a _;_ a \ c0) = (upaco2 c_eq r)=
  \big[Plus/Empt]_a (Event a _;_ a \ c1). move=> HH.
 case Hcase:(nu _)=>//. eq_m_left. eq_m_left.
rewrite !big_shape.
move: (index_enum _)=>ef. elim: ef=>//.
move=> a l HQ/=. rewrite !big_cons. apply/c_plus_ctx=>//.
apply/c_fix=>/=. right. apply/CIH. case: (H1 a)=>//.
Qed.

Theorem soundness : forall c0 c1, c0 =C= c1 -> (forall s, Match s c0 <-> Match s c1).
Proof.
move=>c0 c1 /bisim_soundness/equivP=>//. 
Qed.

Theorem completeness : forall c0 c1, (forall s, Match s c0 <-> Match s c1) -> c0 =C= c1.
Proof.
intros. apply bisim_completeness. apply/equivP=>//.
Qed.

End Equivalence_Properties.

Section parseTrees.

Inductive upTree : Type := 
| up_tt : upTree
| up_bot : upTree
| up_singl (a : A) : upTree
| up_inl : upTree -> upTree
| up_inr  : upTree -> upTree
| up_pair  : upTree -> upTree -> upTree
| up_fold : upTree  -> upTree.

Check upTree_rect.

Fixpoint upTree_size p := 
match p with 
| up_tt =>  1 
| up_bot => 1 
| up_singl _ => 1
| up_inl p0 => (upTree_size p0).+1
| up_inr p0 => (upTree_size p0).+1
| up_pair p0 p1=> ((upTree_size p0) + (upTree_size p1)).+1
| up_fold p0 => (upTree_size p0).+1
end.
(*
Fixpoint take_fix_fuel n (f : (upTree -> upTree) -> upTree -> upTree) : (upTree -> upTree) :=
if n is n'.+1 then
 f (take_fix_fuel n' f)
else id.

Fixpoint take_fix_fuel2 n (f : upTree -> (upTree -> upTree) -> upTree) : (upTree -> upTree) :=
fun T =>
if n is n'.+1 then
 f T (take_fix_fuel2 n' f)
else T.

Fixpoint take_fix_fuel3 n (p : upTree) (f : upTree -> (upTree -> upTree) -> upTree) : upTree :=
if n is n'.+1 then
 f p (fun p' => take_fix_fuel3 n' p' f)
else p.


Definition test_f : upTree -> (upTree -> upTree) -> upTree := 
fun T f => 
match T with 
| up_pair T0 T1 => up_pair T0 (up_pair up_bot (f T1))
| _ => T
end.

(*Eval compute in (take_fix_fuel3 0 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel3 1 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel3 2 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel2 2 test_f (up_pair up_tt up_tt)). *)



Definition pRel (p' p : upTree) := upTree_size p' < upTree_size p.

Definition higher_n (n : nat) := (forall p', upTree_size p' < n -> upTree) -> upTree -> upTree.

Inductive D_fix (n : nat) : higher_n n -> Prop :=
| D_next n n' f : n' < n -> D_fix f  -> D_fix f.


Check @Acc_rect.
Check (@Acc_rect upTree pRel (fun p => (forall p', pRel p' p -> upTree) -> upTree -> upTree)).

Check upTree_rect.

Lemma upTree_size1 : forall p, 0 < upTree_size p.
Proof.
elim=>//.
Qed.


(*Lemma Acc_pRel :  forall p, Acc pRel p.
Proof. 
move=> p. move Heq : (upTree_size p)=>n. elim: n p Heq.
case=>//. move=> n IH. case;intros. con;intros. 
move: H. rewrite /pRel. simpl.  move: (upTree_size1 y). lia.
con. intros. move: H. rewrite /pRel. simpl. move: (upTree_size1 y). lia.
con. intros. move: H. rewrite /pRel. simpl. move: (upTree_size1 y). lia.
move: Heq. simpl. case. intro. 
con. intros. apply/IH.
intros. apply/IH.
intros.
rewrite /pRel //=.
inv H.

simpl. simpl. repeat simpl.
con. move=> y.*)

Lemma upTree_size_rect
     : forall P : upTree -> Type,
       (forall u  : upTree, (forall u', pRel u' u -> P u') -> P u) ->
       forall u : upTree, P u.
Proof.
move=> P Hsize u. 
have: Acc pRel u. clear Hsize. 
move Heq : (upTree_size u)=>n. move: n Heq.
suff : forall n : nat, upTree_size u <= n -> Acc (fun p' p : upTree => pRel p' p) u.
intros. eauto.
move=>n. elim: n u.
intros. con. intros. rewrite /pRel in H0. lia.
intros. con. intros. apply/H. rewrite /pRel in H1. lia.
move=>Hacc.
move: u Hacc Hsize. apply: Acc_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.

Definition my_fix (f : (forall u, (forall u' : upTree, pRel u' u -> upTree) -> upTree)) :  upTree -> upTree:=
(upTree_size_rect (fun _ => upTree) f).

Lemma sum_bool p p' :  {pRel p p'} + { ~ pRel p p'}.
Proof. rewrite /pRel. case Heq : (_ <_)=>//. con. done. right. intro. done.
Defined.

Definition test u : (forall u' : upTree, pRel u' u -> upTree) -> upTree  := 
fun f => match u with 
       | up_pair u0 u1 => match sum_bool u0 u with 
                          | left p => f _ p
                          | right p => u
                          end
       | _ => u
       end.

Fixpoint interp d (f : (forall u, (forall u' : upTree, pRel u' u -> upTree) -> upTree)) :  upTree -> upTree  := 
match d with 
| cfix d' => my_fix (interp d')
| cguard (var_dsl 0) => 


Definition myP (p : upTree) :=  (forall p', pRel p' p -> upTree) -> upTree.

Definition guarded_fun u := (forall u' : upTree, pRel u' u -> upTree) -> upTree.





Definition take_my_fix2  (f : forall p, (forall p', pRel p' p -> upTree) -> upTree) : upTree -> upTree := 
fun T => fix my_fix (H : D_fix (f) {struct H} := f (my_fix (proj H))


f (take_mu_fix2 f)

 f p (fun p' => take_fix_fuel3 n' p' f)

Fixpoint take_my_fix (p : upTree) (f : (forall p', pRel p' p -> upTree) -> upTree -> upTree) {struct p} : upTree -> upTree.
refine ( f (take_my_fix _ f)).
 f p (fun p' => take_fix_fuel3 n' p' f)

Fixpoint take_fix_fuel11 (p : upTree) (f : (upTree -> upTree) -> upTree -> upTree) (H : D_fix f p) {struct H} : upTree :=
 f p (fun p' => take_fix_fuel3 n' p' f)

Fixpoint take_fix_fuel22 (p : upTree) (f : upTree -> (upTree -> upTree) -> upTree) (H : D_fix f p) {struct H} : upTree :=
 f p (fun p' => take_fix_fuel3 n' p' f)

Fixpoint take_fix_fuel3 (p : upTree) (f : upTree -> (upTree -> upTree) -> upTree) (H : D_fix p) {struct H} : upTree :=
 f p (fun p' => take_fix_fuel3 n' p' f)

 f p (take_fix_fuel3 f)

Eval compute in (take_fix_fuel3 0 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel3 1 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel3 2 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel2 2 test_f (up_pair up_tt up_tt)). 


Eval compute in (take_fix_fuel3 4 (up_pair up_tt up_tt) test_f).


Fixpoint take_fix_fuel2 (f : forall p, (forall p', pRel p' p -> upTree) -> upTree) : (upTree -> upTree).


Fixpoint take_fix_fuel n (f : (upTree -> upTree) -> upTree -> upTree) : (upTree -> upTree) :=


 (f : forall p', upTree_size p' < upTree_size p -> upTree) : upTree := 


Definition take_fix (p : upTree) (f : forall p', upTree_size p' < upTree_size p -> upTree) : upTree := 


Section size_eliminator_for_upTree.
  Variable P : ∀x, 𝔻ns x -> Type.


Section eliminator_for_𝔻ns.

  Variable P : ∀x, 𝔻ns x -> Type.

  Hypothesis (HPi : ∀x D1 D2, P x D1 → P x D2)
             (HP0 : ∀x E, P _ (𝔻ns_tt x E))
             (HP1 : ∀x E D, P _ D → P _ (𝔻ns_ff x E D)).

  Fixpoint 𝔻ns_rect x D { struct D } : P x D.
  Proof.
    case_eq (b x); intros G.
    + apply HPi with (1 := HP0 _ G).
    + apply HPi with (1 := HP1 _ G _ (𝔻ns_rect _ (𝜋_𝔻ns D G))).
  Qed.

End eliminator_for_𝔻ns.



Lemma test : forall (P : upTree -> Type), (forall p, (forall p', upTree_size p' < upTree_size p -> P p') -> P p) -> forall (p : upTree), P p.
Proof.
move=> P Hsize p. move Heq: (upTree_size p) => n. move: n p Heq.
fix IH 1. 
case.
- clear IH. case=>//=. 
- move=> n p Heq. apply/Hsize.
  
case=>//=. 

 Check upTree_rect.
apply: upTree_rect.
Check upTree_ind.
apply: upTree_rect.
- move=> H.
*)
Definition upTree_indDef := [indDef for upTree_rect].
Canonical upTree_indType := IndType upTree upTree_indDef.

Definition upTree_hasDecEq := [derive hasDecEq for upTree].
HB.instance Definition _ := upTree_hasDecEq.


Inductive typing : upTree -> regex  -> Prop := 
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


(*Inductive pTree (r : regex) :  Type := 
| p_tt : Eps = r -> pTree r
| p_to : pTree r.

End parseTrees.
End Regex.


Inductive pTree regex : Type := 
| p_tt : pTree Eps 
| p_singl a : pTree (Event a)
| p_inl r0 r1 : pTree r0 -> pTree (r0 _+_ r1) 
| p_inr r0 r1 : pTree r1 -> pTree (r0 _+_ r1) 
| p_pair r0 r1 : pTree r0 -> pTree r1 -> pTree (r0 _;_ r1)
| p_fold r : pTree (Eps _+_ (r _;_ (Star r))) -> pTree (Star r).
Arguments p_inl {r0 r1}.
Arguments p_inr {r0 r1}.
Arguments p_pair {r0 r1}.
Arguments p_fold {r}.*)


(*Fixpoint to_upTree {r : regex} (p : pTree r) : upTree := 
match p with 
| p_tt => up_tt
| p_singl a => up_singl a 
| p_inl _ _ p => up_inl (to_upTree p) 
| p_inr _ _ p => up_inr (to_upTree p)
| p_pair _ _ p0 p1 => up_pair (to_upTree p0) (to_upTree p1)
| p_fold _ p' => up_fold (to_upTree p')
end.*)

(*Lemma typing_to_upTree : forall r (x : pTree r), typing (to_upTree x) r.
Proof.
move=> r. elim=>//=;eauto.
Qed.*)


(*Fixpoint to_pTree {p : upTree} {r : regex} (H : typing p r) : pTree r := 
match H in typing p r return pTree r  with 
| pt_tt => p_tt
| pt_singl a => p_singl a 
| pt_inl _ _ _ p => p_inl (to_pTree p) 
| pt_inr _ _ _ p => p_inr (to_pTree p)
| pt_pair _ _ _ _ p0 p1 => p_pair (to_pTree p0) (to_pTree p1)
| pt_fold _ _ p' => p_fold (to_pTree p')
end.


Fixpoint flatten {r : regex} (T : pTree r) : seq A := 
match T with 
| p_tt => nil 
| p_singl a => (a :: nil )
| p_inl _ _ T' => flatten T'
| p_inr _ _ T' => flatten T'
| p_pair _ _ T0 T1 => (flatten T0) ++ (flatten T1)
| p_fold _ T' => flatten T' 
end.*)

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

(*Lemma uflatten_to_upTree : forall r (x : pTree r),  uflatten (to_upTree x) = flatten x.
Proof.
move=> r. elim=>//=.
move=> r0 r1 p Hf p0 Hf1. rewrite Hf Hf1 //.
Qed.*)

(* Lemma flatten_to_pTree : forall r (x : upTree) (H: typing x r), flatten (to_pTree H) = uflatten x.
Proof.
move=> r x. elim=>//=;eauto;intros.
rewrite H H0. done.
Qed.*)



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

Check flatten.

Lemma exists_pTree : forall r s, Match s r -> exists (T : upTree), (typingb T r) &&  (uflatten T == s).
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

Lemma has_sig : forall (A : eqType) (f : A -> bool) (l :seq A), has f l -> { a | f a}.
Proof.
move => A' f. elim=>//.
move=> a l H. rewrite /=. destruct (f a) eqn:Heqn. move=>_.  econ. eauto.
simpl. eauto.
Defined.

Lemma Match_exists_n : forall s r, Match s r -> exists n, has (fun x => (typingb x r) && (uflatten x == s)) (gen_upTree n).  
Proof.
move=> s r HM. case: (exists_pTree  HM)=> x Hf.
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
Check typing.
Print typing.
Parameter (p : upTree) (r : regex).
(*Check (typing p r : Prop). *) Print Finite.axioms_.
Lemma Match_pTree : forall r s, Match s r -> { T : upTree | prod (typingb T r) (uflatten T == s)}.
Proof.
move => r s HM.
move: (Match_sig_n  HM)=>[]n. move/has_sig=>[] x.
case Hcase: (typingb _ _)=>//=.
move/typingP1 : Hcase=>Ht.
move/eqP=>Hu. exists x. con. apply/typingP2=>//. apply/eqP. done.
Qed.
End parseTrees.
(*Arguments p_inl {r0 r1}.
Arguments p_inr {r0 r1}.
Arguments p_pair {r0 r1}.
Arguments p_fold {r}.*)

Arguments pt_inl {r0 r1 p}.
Arguments pt_inr {r0 r1 p}.
Arguments pt_pair {r0 r1 p0 p1}.
Arguments pt_fold {r p}.
Hint Constructors typing.

Section Containment.
  Variable P : regex -> regex -> dsl -> Prop.
Reserved Notation "c0 <R= c1 ~> p" (at level 63).

(*Tried as much as possible to stay within Henglein & Nielsen's formulation*)
(*full_unf pf = ... ensures that pf <> pfix f. f
  With an explicit fix rule, we would need to ensure guardedness*)
Inductive c_ineq : regex -> regex -> dsl -> Prop :=
| rule_shuffle c0 c1 c2 pf : full_unf pf = shuffle -> (c0 _+_ c1) _+_ c2 <R= c0 _+_ (c1 _+_ c2) ~> pf (*assoc  + *)


| rule_shuffleinv c0 c1 c2 pf : full_unf pf = shuffleinv -> c0 _+_ (c1 _+_ c2)  <R= (c0 _+_ c1) _+_ c2 ~> pf (*assoc +*)

| rule_retag c0 c1 pf: full_unf pf = retag -> c0 _+_ c1 <R= c1 _+_ c0 ~> pf (*comm +*)(*Other direction is redundant*)

| rule_untagL c pf : full_unf pf = untagL -> Empt _+_ c <R= c ~> pf (* + neut r*)
| rule_untagLinv c pf: full_unf pf = untagLinv -> c <R= Empt _+_ c ~> pf (*Possibly redundant*)

| rule_untag c pf : full_unf pf = untag ->  c _+_ c <R= c ~> pf (*idem*)
| rule_tagL c d pf : full_unf pf = tagL ->  c <R= c _+_ d ~> pf

| rule_assoc c0 c1 c2 pf : full_unf pf = assoc ->  (c0 _;_ c1) _;_ c2 <R= c0 _;_ (c1 _;_ c2) ~> pf
| rule_associnv c0 c1 c2 pf : full_unf pf = associnv -> c0 _;_ (c1 _;_ c2) <R=  (c0 _;_ c1) _;_ c2 ~> pf

| rule_swap c pf : full_unf pf = swap -> (c _;_ Eps) <R= (Eps _;_ c) ~> pf (*New rule, from regex as types paper*)
| rule_swapinv c pf : full_unf pf = swapinv -> (Eps _;_ c) <R= (c _;_ Eps) ~> pf

| rule_proj c pf : full_unf pf = proj -> (Eps _;_ c) <R= c ~> pf
| rule_projinv c pf : full_unf pf = projinv -> c <R=(Eps _;_ c) ~> pf

| rule_abortR c pf : full_unf pf = abortR ->  c _;_ Empt <R= Empt ~> pf
| rule_abortRinv c pf : full_unf pf = abortRinv ->  Empt  <R= c _;_ Empt ~> pf

| rule_abortL c pf : full_unf pf = abortL -> Empt _;_ c <R=  Empt ~> pf
| rule_abortLinv c pf : full_unf pf = abortLinv -> Empt  <R=  Empt _;_ c ~> pf

| rule_distL c0 c1 c2 pf : full_unf pf = distL -> c0 _;_ (c1 _+_ c2) <R= (c0 _;_ c1) _+_ (c0 _;_ c2) ~> pf
| rule_distLinv c0 c1 c2 pf : full_unf pf = distLinv -> (c0 _;_ c1) _+_ (c0 _;_ c2)  <R=  c0 _;_ (c1 _+_ c2) ~> pf

| rule_distR c0 c1 c2 pf : full_unf pf = distR -> (c0 _+_ c1) _;_ c2 <R= (c0 _;_ c2) _+_ (c1 _;_ c2) ~> pf
| rule_distRinv c0 c1 c2 pf : full_unf pf = distRinv ->  (c0 _;_ c2) _+_ (c1 _;_ c2)  <R= (c0 _+_ c1) _;_ c2 ~> pf


| rule_wrap c pf : full_unf pf = wrap ->  Eps _+_ (c _;_ Star c) <R= Star c ~> pf
| rule_wrapinv c pf : full_unf pf = wrapinv -> Star c  <R=Eps _+_ (c _;_ Star c) ~> pf

| rule_drop c pf : full_unf pf = drop ->  Star (Eps _+_ c) <R= Star c ~> pf
| rule_dropinv c pf : full_unf pf = dropinv ->  Star c <R= Star (Eps _+_ c) ~> pf (*Possibly redundant*)

 (*We want to remove inner Eps, so we only keep this one for now*)
(*Will the other direction be necessary?*)
(*| ci_star_plus_inv c :  Star c  <R= Star (Eps _+_ c) (*Could possibly be removed but we are studying the computational interpretation of EQ rules*) *)

| rule_cid c pf : full_unf pf = cid ->  c <R= c ~> pf

(*| ci_sym c0 c1 (H: c0 =R=c1) : c1 =R=c0*)
| rule_ctrans c0 c1 c2 pf p0 p1 : full_unf pf =  ctrans p0 p1 ->  c0 <R=c1 ~> p0 ->  c1 <R=c2 ~> p1 -> c0 <R=c2 ~> pf
| rule_cplus c0 c0' c1 c1' pf p0 p1 : full_unf pf = cplus p0 p1 ->  c0 <R=c0' ~> p0 -> c1 <R=c1' ~> p1 -> c0 _+_ c1 <R=c0' _+_ c1' ~> pf
| rule_cseq c0 c0' c1 c1' pf p0 p1 : full_unf pf = cseq p0 p1 ->  c0 <R=c0' ~> p0 -> c1 <R=c1' ~> p1 ->  c0 _;_ c1 <R=c0' _;_ c1' ~> pf
| rule_cstar c0 c1 pf p : full_unf pf = cstar p ->  c0 <R=c1 ~> p -> Star c0 <R= Star c1 ~> pf  (*new context rule*) 
(*| rule_cfix r r' (p  : dsl) : r <R= r' ~> p[d (cfix p) .: var_dsl] ->  r <R= r' ~> (cfix p) (*guarded p otherwise unsound*)*)
| rule_test a r r' pf p : full_unf pf = guard p -> P r r' p -> (Event a) _;_ r <R= (Event a) _;_ r' ~> pf
 where "c1 <R= c2 ~> p" := (c_ineq c1 c2 p).
End Containment.

Notation "c0 < ( R ) = c1 ~> p" := (c_ineq R c0 c1 p)(at level 63).
Definition INEQ c0 c1 p := paco3 c_ineq bot3 c0 c1 p.
Notation "c0 <C= c1 ~> p" := (INEQ c0 c1 p)(at level 63).


(*Section DSL.
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
(*| rule_cfix r r' (p  : dsl R dsl) : dsl R r  r' ~> p[d (cfix p) .: dsl R var_dsl] ->  r  r' ~> (cfix p) (*guarded p otherwise unsound*)*)
| guard a A B  : R A B -> dsl R ((Event a) _;_ A)  ((Event a) _;_ B).
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
Arguments guard {R a A B}.


CoInductive dsl_co : regex -> regex -> Type := 
| Co_build A B : (dsl dsl_co) A B -> dsl_co A B.
(*Arguments Co_build {A B}.*)


CoFixpoint co_test :=  Co_build (trans shuffle (guard co_test))*)

(*Inductive star (A : Type) := 
fold_s : (unit + (A * (star A))) -> star A.
Arguments fold_s {A}.
Definition unfold_s (A : Type) : star A -> (unit + (A * (star A))) :=
fun T => let: fold_s T' := T in T'.
Arguments unfold_s{A}.

Inductive singleton (A : Type) (a : A) : Type := 
| build_single.

Fixpoint as_type (r : regex) : Type := 
match r with 
| Eps => unit 
| Empt => void
| Event a => singleton _ a
| Plus r0 r1 => (as_type r0) + (as_type r1)
| Seq r0 r1 => (as_type r0) * (as_type r1)
| Star r0 => star (as_type r0)
end.*)


(*Fixpoint to_as_type {r : regex} (p : pTree r) : (as_type r) := 
match p in pTree r return as_type r with 
| p_tt => tt
| p_singl a => build_single _ a
| p_inl _ _ p0 => inl (to_as_type p0)
| p_inr _ _ p1 => inr (to_as_type p1)
| p_pair _ _ p0 p1 => pair (to_as_type p0) (to_as_type p1)
| p_fold _ p0 => fold_s (to_as_type p0)
end.

Fixpoint from_as_type {r : regex} (p: as_type r) : pTree r := 
match r as r' return match r withpTree r' with 
| Eps => p_tt
| Empt => match p with end
| Event a => p_singl a
| Plus p0 p1 => match p with | inl p0 => p_inl _ _ (from_as_type p0) | inr p1 => p_inr _ _ (from_as_type p1) end 
| Seq p0 p1 => match p with | pair p0 p1 => p_pair _ _ (from_as_type p0) (from_as_type p1) end
| Star p => match p with | fold_s p0 => p_fold _ (from_as_type p0) end 
end.
match p return pTree r with
| tt => p_tt
| build_single  =>  p_singl _
| inl p0 =>  p_inl _ _ (from_as_type p0)
| inr p1 =>  p_inr _ _ (from_as_type p1 )
|pair p0 p1 =>  p_pair _ _ (from_as_type p0) (from_as_type p1)
| fold_s p0 => p_fold _ (from_as_type p0)
end.*)

(*Notation "c0 <T= c1" := ((pTree c0) -> (pTree c1))(at level 63).
Notation "c0 <O= c1 ~> p" := ((pTree c0) -> option (pTree c1))(at level 63).*)


(*Print pair.

Print pTree.

Check pTree_ind.

Print p_tt.
Check @p_inl.

Check pTree_rect.
Require Import Coq.Program.Equality.
*)

Notation "c0 <T= c1 ~> p" := (forall s, typing s c0 -> typing (p s) c1)(at level 63).

Definition fType :=  upTree -> upTree. 
Ltac inve H := inversion_clear H;subst;eauto.
Ltac lt_once := (match goal with 
                 | [ H : typing _ (_ _+_ _) |- _] => inve H
                 | [ H : typing _ (_ _;_ _) |- _] => inve H
                 | [ H : typing _ (Star _) |- _] => inve H
                 | [ H : typing _ Eps |- _] => inve H
                 | [ H : typing _ Empt |- _] => inve H
                 | [ H : typing _ (Event _) |- _] => inve H

                end).
Ltac lt := cbv;solve[ eauto | intros;repeat lt_once].

(*(A' _+_ B) _+_ C <T= A' _+_ (B _+_ C).*)
Definition shuffle_i  : fType := 
fun  T => 
match T with
| up_inl (up_inl T') => (up_inl T')
| up_inl (up_inr T') => (up_inr (up_inl T'))
| up_inr T' =>  (up_inr (up_inr T'))
| _ => up_bot
end.
Lemma shuffle_i_t  : forall A B C,(A _+_ B) _+_ C <T= A _+_ (B _+_ C) ~> shuffle_i.
Proof. lt. Qed.


(* A _+_ (B _+_ C)  <T= (A _+_ B) _+_ C*)
Definition shuffleinv_i  : fType :=
fun  T => 
match T with 
| up_inl T' => (up_inl (up_inl T'))
| up_inr (up_inl T') => (up_inl (up_inr T'))
| up_inr (up_inr T') =>  ((up_inr T'))
| _ => up_bot
end.
Lemma shuffleinv_i_t : forall A B C,   A _+_ (B _+_ C)  <T= (A _+_ B) _+_ C ~> shuffleinv_i.
Proof. lt. Qed.


(* A _+_ B <T= B _+_ A *)
Definition retag_i :  fType  :=
fun T => 
match T with 
| up_inl T' => up_inr T' 
| up_inr T' => up_inl T'
| _ => up_bot
end. 
Lemma retag_i_t : forall A B,  A _+_ B <T= B _+_ A  ~> retag_i.
Proof. lt. Qed.

(*Empt _+_ A <T= A*)
Definition untagL_i :  fType :=
fun T => 
match T with 
| up_inl T' => match T' with | _ => up_bot  end 
| up_inr T' => T' 
| _ => up_bot
end.
Lemma untagL_i_t : forall A, Empt _+_ A <T= A ~> untagL_i.
Proof. lt. Qed.

(* A <T= Empt _+_ A*)
Definition untagLinv_i :  fType :=
fun T => up_inr T.
Lemma untagLinv_i_t : forall A,  A <T= Empt _+_ A ~> untagLinv_i.
Proof. lt. Qed.

(*A _+_ A <T= A*)
Definition untag_i :  fType  :=
fun T =>
match T with 
| up_inl T' => T'
| up_inr T' => T'
| _ => up_bot
end.
Lemma untag_i_t : forall A, A _+_ A <T= A ~> untag_i.
Proof. lt. Qed.

(* A <T= (A _+_ B ) *)
Definition tagL_i : fType  := up_inl.
Lemma tagL_i_t : forall A B,  A <T= (A _+_ B ) ~>tagL_i.
Proof. lt. Qed.

(* ((A _;_ B) _;_ C)<T=  (A _;_ (B _;_ C))*)
Definition assoc_i : fType := 
fun T => 
match T with 
| up_pair (up_pair T0 T1) T2 => up_pair T0 (up_pair T1 T2)
| _ => up_bot 
end.
Lemma assoc_i_t : forall A B C, ((A _;_ B) _;_ C)<T=  (A _;_ (B _;_ C)) ~> assoc_i.
Proof. lt. Qed.

(*(A _;_ (B _;_ C)) <T=  ((A _;_ B) _;_ C)*)
Definition associnv_i : fType  :=
fun T => 
match T with 
| up_pair T0 (up_pair T1 T2) => up_pair (up_pair T0 T1) T2
| _ => up_bot
end.
Lemma associnv_i_t : forall A B C, (A _;_ (B _;_ C)) <T=  ((A _;_ B) _;_ C) ~> associnv_i.
Proof. lt. Qed.

(* (A _;_ Eps)<T=  (Eps _;_ A) *)
Definition swap_i : fType := 
fun T => 
match T with 
| up_pair T0 up_tt => up_pair up_tt T0
| _ => up_bot 
end.
Lemma swap_i_t : forall A,  (A _;_ Eps)<T=  (Eps _;_ A) ~> swap_i.
Proof. lt. Qed.

(* (Eps _;_ A) <T= (A _;_ Eps)*)
Definition swapinv_i : fType := 
fun T => 
match T with 
| up_pair up_tt T' => up_pair T' up_tt
| _ => up_bot
end.
Lemma swapinv_i_t : forall A, (Eps _;_ A) <T= (A _;_ Eps) ~> swapinv_i.
Proof. lt. Qed.

(* (Eps _;_ A)<T=  A*)
Definition proj_i : fType := 
fun T => 
match T with 
| up_pair up_tt T' => T'
| _ => up_bot
end.
Lemma proj_i_t : forall A, (Eps _;_ A)<T=  A ~> proj_i.
Proof. lt. Qed.

(* A <T= (Eps _;_ A)*)
Definition projinv_i : fType := 
fun T => up_pair up_tt T.
Lemma projinv_i_t : forall A,  A <T= (Eps _;_ A) ~> projinv_i.
Proof. lt. Qed.

(*Does this make sense, the domain is empty*)
(* (A _;_ Empt) <T=  Empt*)
Definition abortR_i : fType := 
fun _ => up_bot.
Lemma abortR_i_t : forall A, (A _;_ Empt) <T=  Empt ~> abortR_i.
Proof. lt. Qed.
(*match T with 
| up_pair T' up_bot => up_bot
| _ => up_bot
end. *)

(*Empt  <T=  (A _;_ Empt)*)
Definition abortRinv_i : fType  := fun _ => up_bot.
Lemma abortRinv_i_t : forall A, Empt  <T=  (A _;_ Empt) ~> abortRinv_i.
Proof. lt. Qed.
(*fun T => 
match T with end.*)

(* (Empt _;_ A) <T=  Empt*)
Definition abortL_i : fType := fun _ => up_bot.
Lemma abortL_i_t : forall A,  (Empt _;_ A) <T=  Empt ~> abortL_i.
Proof. lt. Qed.
(*fun T => match T.1 with end.*)

(* Empt <T=   (Empt _;_ A) *)
Definition abortLinv_i : fType := fun _ => up_bot.
Lemma abortLinv_i_t : forall A, Empt <T=   (Empt _;_ A) ~>abortLinv_i.
Proof. lt. Qed.
(*fun T => match T with end.*)

(*(A _;_ (B _+_ C)) <T= ((A _;_ B) _+_ (A _;_ C))*)
Definition distL_i : fType := 
fun T => 
match T with 
| up_pair T0 (up_inl T1) => up_inl (up_pair T0 T1)
| up_pair T0 (up_inr T1) => up_inr (up_pair T0 T1)
| _ => up_bot 
end.
Lemma distL_i_t : forall A B C, (A _;_ (B _+_ C)) <T= ((A _;_ B) _+_ (A _;_ C)) ~>distL_i.
Proof. lt. Qed.

(* ((A _;_ B) _+_ (A _;_ C)) <T= (A _;_ (B _+_ C))*)
Definition distLinv_i : fType :=
fun T => 
match T with 
| up_inl (up_pair T0 T1) => up_pair T0 (up_inl T1)
| up_inr (up_pair T0 T1) => up_pair T0 (up_inr T1)
| _ => up_bot
end.
Lemma distLinv_i_t : forall A B C, ((A _;_ B) _+_ (A _;_ C)) <T= (A _;_ (B _+_ C)) ~>distLinv_i.
Proof. lt. Qed.


(* ((A _+_ B) _;_ C) <T=  ((A _;_ C) _+_ (B _;_ C))*)
Definition distR_i : fType :=
fun T => 
match T with 
| up_pair (up_inl T') T1 => up_inl (up_pair T' T1)
| up_pair (up_inr T') T1 => up_inr (up_pair T' T1)
| _ => up_bot
end.
Lemma distR_i_t : forall A B C, ((A _+_ B) _;_ C) <T=  ((A _;_ C) _+_ (B _;_ C)) ~>distR_i.
Proof. lt. Qed.
(*let: (T0,T1) := T in 
match T0 with 
| up_inl T' => up_inl (T',T1)
| up_inr T' => up_inr (T',T1)
end.*)

(* ((A _;_ C) _+_ (B _;_ C))  <T= ((A _+_ B) _;_ C) *)
Definition distRinv_i : fType :=
fun T => 
match T with 
| up_inl (up_pair T0 T1) => up_pair (up_inl T0) T1
| up_inr (up_pair T0 T1) => up_pair (up_inr T0) T1
| _ => up_bot
end.
Lemma distRinv_i_t : forall A B C,  ((A _;_ C) _+_ (B _;_ C))  <T= ((A _+_ B) _;_ C) ~>distRinv_i.
Proof. lt. Qed.

(*(Eps _+_ (A _;_ Star A)) <T= (Star A)*)
Definition wrap_i : fType  := up_fold.
Lemma wrap_i_t : forall A,(Eps _+_ (A _;_ Star A)) <T= (Star A) ~>wrap_i.
Proof. lt. Qed.
(*fun T => 
match T with
| p_inl _ => nil 
| p_inr (T0,T1) => cons T0 T1
end.*)


(* (Star A) <T= (Eps _+_ (A _;_ Star A))*)
Definition wrapinv_i : fType := 
fun T => 
match T with 
| up_fold T' => T'
| _ => up_bot
end.
Lemma wrapinv_i_t : forall A, (Star A) <T= (Eps _+_ (A _;_ Star A)) ~>wrapinv_i.
Proof. lt. Qed.

(*fun T => 
match T with 
| nil => p_inl tt
| cons a T' => p_inr (a,T')
end.*)

(*(Star (Eps _+_ A)) <T= (Star A) *)
Definition drop_i : fType  :=
fix drop_i T := 
match T with 
| up_fold T0 => match T0 with 
               | up_inl up_tt => up_fold (up_inl up_tt)
               | up_inr T1 => match T1 with 
                              | up_pair T2 T3 => match T2 with 
                                                  | up_inl up_tt => drop_i T3
                                                  | up_inr T4 => up_fold (up_inr (up_pair T4 (drop_i T3)))
                                                  | _ => up_bot
                                                 end
                              | _ => up_bot
                             end
               | _ => up_bot
               end
| _ => up_bot
end.


(*Need size induction on T*)
Lemma drop_i_t : forall A, (Star (Eps _+_ A)) <T= (Star A) ~>drop_i.
Proof.
move=> r T. move Heq: (upTree_size T) => n. move: Heq. suff: upTree_size T <= n -> typing T (Star (Eps _+_ r)) -> typing (drop_i T) (Star r).
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. inv H4. inv H3. apply/IH. ssa. done.
con. con. con. done. apply/IH. ssa. lia. done.
Qed.

(*Lemma test_drop_i_input : forall a, typing 
    (up_fold (up_inr (up_pair (up_inr (up_singl a)) (up_fold (up_inr (up_pair (up_inl up_tt) (up_fold (up_inl up_tt))))))))
    (Star (Eps _+_ (Event a))).
Proof.
move=> a. repeat con. 
Qed.

(*Eval compute in (drop_i test).*)

Lemma test_drop_i_output : forall a, typing 
    (up_fold (up_inr (up_pair (up_singl a) (up_fold (up_inl up_tt)))))
    (Star ((Event a))).
Proof.
move=> a. repeat con. 
Qed.*)
(*Test suceeded*)

(*match wrapinv_i T with
| up_inl _ => wrap_i (up_inl up_tt)
| up_inr (up_pair (up_inl up_tt) T') => wrap_i (up_inl up_tt)
| up_inr T0 => match T0 with 
               | (up_pair (up_inr T1) T2) => wrap_i (up_inr (up_pair T1 (drop_i T2)))
               | _ => up_bot
              end
| _ => up_bot
end.
Fixpoint drop_i : fType  :=
fix drop_i T := 
match unfold_s T with
| up_inl _ => fold_s (up_inl tt)
| up_inr (a,T') => match a with | up_inl tt => fold_s (up_inl tt) | up_inr a' => fold_s (up_inr (a',drop_i T')) end
end.*)

(* (Star A) <T= (Star (Eps _+_ A))*)
Definition dropinv_i : fType :=
fix dropinv_i T := 
match T with 
| up_fold T0 => match T0 with 
                | up_inl up_tt => up_fold (up_inl up_tt)
                | up_inr T1 => match T1 with 
                               | up_pair T2 T3 => up_fold (up_inr (up_pair (up_inr T2) (dropinv_i T3)))
                               | _ => up_bot 
                              end 
                | _ => up_bot 
                end 
| _ => up_bot 
end.
Lemma dropinv_i_t : forall A, (Star A) <T= (Star (Eps _+_ A)) ~> dropinv_i.
Proof. 
move=> r T. move Heq: (upTree_size T) => n. move: Heq. suff: upTree_size T <= n ->typing T (Star r) -> typing (dropinv_i T) (Star (Eps _+_ r)).
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. con. con. con. con. done. apply/IH. ssa. lia. eauto.
Qed.

(*match unfold_s T with 
| up_inl _ => fold_s (up_inl tt)
| up_inr (a,T') => fold_s (up_inr (up_inr a,dropinv_i T'))
end.*)

(* A <T= A *)
Definition cid_i : fType := fun x => x.
Lemma cid_i_t : forall A, A <T= A ~>cid_i.
Proof. lt. Qed.


(* (f0 : A <T=  A') (f1 : B <T= B') : (A _;_ B) <T= (A' _;_ B') *)
Definition cseq_i (f0 f1 : fType ) : fType :=
fun T => 
match T with 
| up_pair T0 T1 => up_pair (f0 T0) (f1 T1)
| _ => up_bot 
end. 
Lemma cseq_i_t : forall A A' B B' f0 f1, A <T=  A' ~> f0 -> B <T= B' ~> f1 -> (A _;_ B) <T= (A' _;_ B') ~> (cseq_i f0 f1).
Proof. lt. Qed.
(*let: (T0,T1) := T in (f0 T0, f1 T1).*)

(* (f : A <T= B) : (Star A)  <T= (Star B) *)
(*Definition cstar_i2 (f : fType) : fType := 
match T with 
| up_fold *)

(*match unfold_s T with 
| up_inl _ => fold_s (up_inl tt)
| up_inr (a,T') => fold_s (up_inr (f a,(cstar_i T')))
end.*)

(* (f : A <T=B) (f' :B <T=C) :  A <T=C*)
Definition ctrans_i (f f' : fType) :  fType :=
f' \o f.
Lemma ctrans_i_t : forall A B C f f', A <T=B ~> f ->  B <T=C ~>f' ->  A <T=C ~> (ctrans_i f f').
Proof. lt. Qed.

(* (f :  A <T=A' ) (f' :  B <T=B' ) : A _+_ B <T=A' _+_ B'*)
Definition cplus_i (f f' :  fType)  : fType :=
fun T => 
match T with 
| up_inl T' => up_inl (f T')
| up_inr T' => up_inr (f' T')
| _ => up_bot
end.
Lemma cplus_i_t : forall A A' B B' f f', A <T=A' ~> f -> B <T=B'  ~> f'  -> A _+_ B <T=A' _+_ B' ~> (cplus_i f f').
Proof. lt. Qed.




(*Definition shuffle_o A B C : (A _+_ B) _+_ C <O= A _+_ (B _+_ C) := Some \o shuffle_i.  
Definition shuffleinv_o A B C :  A _+_ (B _+_ C)  <O= (A _+_ B) _+_ C := Some \o shuffleinv_i.

Definition retag_o A B : A _+_ B <O= B _+_ A := Some \o retag_i.

Definition untagL_o A : Empt _+_ A <O= A := Some \o untagL_i.
Definition untagLinv_o A : A <O= Empt _+_ A := Some \o untagLinv_i.

Definition untag_o A : A _+_ A <O= A := Some \o untag_i.

Definition tagL_o A B :  A <O= (A _+_ B ) := Some \o tagL_i.

Definition assoc_o A B C : ((A _;_ B) _;_ C)<O=  (A _;_ (B _;_ C)) := Some \o assoc_i.
Definition associnv_o A B C : (A _;_ (B _;_ C)) <O=  ((A _;_ B) _;_ C) := Some \o associnv_i.

Definition swap_o A :  (A _;_ Eps)<O=  (Eps _;_ A) := Some \o swap_i.
Definition swapinv_o A : (Eps _;_ A) <O= (A _;_ Eps) := Some \o swapinv_i.

Definition proj_o A : (Eps _;_ A)<O=  A := Some \o proj_i.
Definition projinv_o A : A <O= (Eps _;_ A) := Some \o projinv_i.

Definition abortR_o A : (A _;_ Empt) <O=  Empt := fun T => match T.2 with end.
Definition abortRinv_o A : Empt  <O=  (A _;_ Empt) := fun T => match T with end.

Definition abortL_o A : (Empt _;_ A) <O=  Empt := fun T => match T.1 with end.
Definition abortLinv_o A : Empt <O=   (Empt _;_ A) := fun T => match T with end.

Definition distL_o A B C : (A _;_ (B _+_ C)) <O= ((A _;_ B) _+_ (A _;_ C)) := Some \o distL_i.
Definition distLinv_o A B C :  ((A _;_ B) _+_ (A _;_ C)) <O= (A _;_ (B _+_ C)) := Some \o distLinv_i.

Definition distR_o A B C : ((A _+_ B) _;_ C) <O=  ((A _;_ C) _+_ (B _;_ C)) := Some \o distR_i.
Definition distRinv_o A B C : ((A _;_ C) _+_ (B _;_ C))  <O= ((A _+_ B) _;_ C) := Some \o distRinv_i.

Definition wrap_o A : (Eps _+_ (A _;_ Star A)) <O= (Star A) := Some \o wrap_i.
Definition wrapinv_o A : (Star A) <O= (Eps _+_ (A _;_ Star A)) := Some \o wrapinv_i.

Definition drop_o A :  (Star (Eps _+_ A)) <O= (Star A) := Some \o drop_i.
Definition dropinv_o A : (Star A) <O= (Star (Eps _+_ A)) := Some \o dropinv_i.

Definition cid_o {c} : c <O= c := fun x => Some x.

Definition cseq_o A A' B B'  (f0 : A <O=  A') (f1 : B <O= B') : (A _;_ B) <O= (A' _;_ B') :=
fun T => let: (T0,T1) := T in if (f0 T0, f1 T1) is (Some T0',Some T1') then Some (T0',T1') else None.

Definition cstar_o A B (f : A <O= B) : (Star A)  <O= (Star B) := 
fix cstar_i T := 
match unfold_s T with 
| p_inl _ => Some (fold_s (p_inl tt))
| p_inr (a,T') => if (f a,cstar_i T') is (Some b,Some T') then Some (fold_s (p_inr (b,(T')))) else None
end.
(*fix cstar_o T := 
match T with 
| nil => Some nil 
| cons a b => if (f a,cstar_o b) is (Some b, Some T') then Some (b::T') else None 
end.*)


Definition ctrans_o {c0 c1 c2} (f : c0 <O=c1) (f' :c1 <O=c2) :  c0 <O=c2 :=
 (obind f') \o f. 


Definition cplus_o {c0 c1 c0' c1'} (f :  c0 <O=c0' ) (f' :  c1 <O=c1' ) : c0 _+_ c1 <O=c0' _+_ c1' :=
fun T => 
match T with 
| p_inl T' => omap p_inl (f T')
| p_inr T' => omap p_inr (f' T')
end.*)

(*(f : A <O= B) : ((Event a) _;_ A) <O= ((Event a) _;_ B)*)
Definition guard_i (f : fType) : fType := 
fun T => 
match T with 
| up_pair (up_singl a) T' => up_pair (up_singl a) (f T') 
| _ => up_bot 
end.
Lemma guard_i_t : forall a A B f, A <T= B ~> f  -> ((Event a) _;_ A) <T= ((Event a) _;_ B) ~> (guard_i f).
Proof. lt. Qed.

Hint Resolve shuffle_i_t shuffleinv_i_t retag_i_t untagL_i_t untagLinv_i_t untag_i_t
             tagL_i_t assoc_i_t associnv_i_t swap_i_t swapinv_i_t proj_i_t projinv_i_t abortR_i_t
             abortRinv_i_t abortL_i_t abortLinv_i_t distL_i_t distLinv_i_t distR_i_t distRinv_i_t
             wrap_i_t wrapinv_i_t drop_i_t dropinv_i_t cid_i_t ctrans_i_t cplus_i_t cseq_i_t (*cstar_i_t*) guard_i_t.

(*Definition opt_fType := upTree -> option upTree.*)

Fixpoint event_count (a : upTree) :=
match a with 
| up_tt => 0
| up_bot => 0
| up_singl _ => 1
| up_inl a' => event_count a'
| up_inr a' => event_count a'
| up_pair a0 a1 => (event_count a0) + (event_count a1)
| up_fold a0 => event_count a0
end.

(*
| shuffle  => shuffle_i
| shuffleinv => shuffleinv_i


| retag => retag_i
| untagL => untagL_i
| untagLinv => untagLinv_i
| untag => untag_i
| tagL => tagL_i

| assoc    => assoc_i
| associnv    => associnv_i

| swap  =>  swap_i
| swapinv  => swapinv_i

| proj  => proj_i
| projinv  => projinv_i

| abortR  => abortR_i
| abortRinv  => abortRinv_i

| abortL  => abortL_i
| abortLinv => abortLinv_i

| distL    => distL_i
| distLinv    => distLinv_i

| distR    => distR_i
| distRinv    => distRinv_i

| wrap  => wrap_i
| wrapinv  => wrapinv_i

| drop  => drop_i 
| dropinv  => dropinv_i
| cid => cid_i*)

Definition interp_base d := 
match d with 
| shuffle  => Some shuffle_i
| shuffleinv => Some shuffleinv_i


| retag => Some retag_i
| untagL => Some untagL_i
| untagLinv => Some untagLinv_i
| untag => Some untag_i
| tagL => Some tagL_i

| assoc    => Some assoc_i
| associnv    => Some associnv_i

| swap  => Some  swap_i
| swapinv  => Some swapinv_i

| proj  => Some proj_i
| projinv  => Some projinv_i

| abortR  => Some abortR_i
| abortRinv  => Some abortRinv_i

| abortL  => Some abortL_i
| abortLinv => Some abortLinv_i

| distL    => Some distL_i
| distLinv    => Some distLinv_i

| distR    => Some distR_i
| distRinv    => Some distRinv_i

| wrap  => Some wrap_i
| wrapinv  => Some wrapinv_i

| drop  => Some drop_i 
| dropinv  => Some dropinv_i
| cid => Some cid_i
| _ => None
end.


Inductive D_dom : dsl -> nat -> Prop := 
| D_base d f n : interp_base (full_unf d) = Some f -> D_dom d n
| D_trans d d0 d1 n : full_unf d = ctrans d0 d1 -> 
                    D_dom d0 n -> D_dom d1 n ->  D_dom d n
(*| D_trans d d0 d1 T : full_unf d = ctrans d0 d1 -> 
                    D_dom d0  T -> (forall T',  D_dom d1 T') -> D_dom d T*)
| D_plus d d0 d1 n : full_unf d = (cplus d0 d1) ->  D_dom d0 n -> D_dom d1 n  -> D_dom d n
| D_seq d d0 d1 n  : full_unf d = (cseq d0 d1) ->  D_dom d0 n -> D_dom d1 n  -> D_dom d n
| D_star d d0 n : full_unf d = cstar d0 -> D_dom d0 n -> D_dom d n
| D_guard d d0 n n' : full_unf d =  guard d0 -> n = n'.+1 ->   D_dom d0 n' -> D_dom d n.
Hint Constructors D_dom.
Check D_trans.
Definition proj_trans0  d d0 d1 n (Heq : full_unf d = ctrans d0 d1) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = ctrans d0 d1 -> D_dom d0 n with 
| D_trans _ _ _ _ Heq Hd Hle => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_trans1  d d0 d1 n (Heq : full_unf d = ctrans d0 d1) (D : D_dom d n)  : D_dom d1 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = ctrans d0 d1 ->   D_dom d1 n  with 
| D_trans _ _ _ _ Heq Hd Hle => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ.  
Defined.

Definition proj_plus0  d d0 d1 n (Heq : full_unf d = cplus d0 d1) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cplus d0 d1 -> D_dom d0 n with 
| D_plus _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_plus1  d d0 d1 n (Heq : full_unf d = cplus d0 d1) (D : D_dom d n) : D_dom d1 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cplus d0 d1 -> D_dom d1 n with 
| D_plus _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.
Check D_seq.
Definition proj_seq0  d d0 d1 n (Heq : full_unf d = cseq d0 d1) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cseq d0 d1 -> D_dom d0 n with 
| D_seq _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_seq1  d d0 d1 n (Heq : full_unf d = cseq d0 d1) (D : D_dom d n) : D_dom d1 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cseq d0 d1 -> D_dom d1 n with 
| D_seq _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_star  d d0 n (Heq : full_unf d = cstar d0) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cstar d0 -> D_dom d0 n with 
| D_star _ _ _ Heq Hd => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.


Definition proj_guard  d d0 n n' (Heq : full_unf d = guard d0) (Hn : n = n'.+1) (D : D_dom d n) : D_dom d0 n'.
Proof. refine(
match D in D_dom d' n return full_unf d' = guard d0 -> n = n'.+1 -> D_dom d0 n' with 
| D_guard _ _ _ _ Heq Hneq Hd => fun HQ Hn => _
| _ => fun HQ Hn => _
end Heq Hn).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. inv Hn. 
Defined.


Fixpoint interp {n} d (D : D_dom d n)  {struct D} :  upTree -> option upTree := 
match full_unf d as d' return full_unf d = d' -> (upTree -> option upTree) with
| ctrans d0 d1 => fun HQ T => 
                  if @interp _ d0 (proj_trans0 HQ D) T is Some T' 
                     then @interp _ d1 (proj_trans1 HQ D) T'
                     else None 
| cplus d0 d1 => fun HQ T=> 
                  match T with 
                 | up_inl T' => omap up_inl (@interp _ d0 (proj_plus0 HQ D) T')
                 | up_inr T' => omap up_inr (@interp _ d1 (proj_plus1 HQ D) T')
                 | _ => None 
                end
| cseq  d0 d1  => fun HQ T=> 
                   match T with 
                   | up_pair T0 T1 => if (@interp _ d0 (proj_seq0 HQ D) T0, @interp _ d1 (proj_seq1 HQ D) T1)
                                         is (Some T',Some T'') then Some (up_pair T' T'') else None
                   | _ => None 
                 end
| cstar d0 => fun HQ T => (fix cstar_i T' {struct T'} := 
                   match T' with 
                      | up_fold T0 => match T0 with 
                                     | up_inl up_tt => Some (up_fold (up_inl up_tt))
                                     | up_inr (up_pair T1 T2) => if (@interp _ d0 (proj_star HQ D) T1, cstar_i T2) 
                                                                     is (Some T',Some T'') then
                                                                  Some ( up_fold (up_inr (up_pair T' T''))) else None
                                     | _ => None
                                     end
                      | _ => None
                      end) T
| guard  d0 => fun HQ T => match n as n0 return n = n0 -> option upTree with 
                        | n'.+1 => fun Hn => match T with
                                         | up_pair (up_singl a) T0 => 
                                             if @interp _ d0 (proj_guard HQ Hn D) T0 is Some T' then Some (up_pair (up_singl a) T') 
                                             else None 
                                                 
                                         | _ => None 
                                         end 
                        | _ => fun _ => None
                       end Logic.eq_refl
| _ => fun HQ T => if interp_base d is Some f then Some (f T) else None
end Logic.eq_refl .


Fixpoint interp_aux d (T : upTree)  {struct d} :  option upTree := 
match full_unf d with
| ctrans d0 d1 => if interp_aux d0 T f is Some T' then interp_aux d T' f else None 
| cplus d0 d1 => match T with 
                 | up_inl T' => interp_aux d0 T' f
                 | up_inr T' => interp_aux d1 T' f
                 | _ => None
                end
| cseq  d0 d1  => match T with 
                   | up_pair T0 T1 => if (interp_aux d0 T0 f,interp_aux d1 T1 f) is (Some T',Some T'') then Some (up_pair T' T'') else None
                   | _ => None 
                 end
| cstar d0 =>  (fix cstar_i T' {struct T'} := 
                   match T' with 
                      | up_fold T0 => match T0 with 
                                     | up_inl up_tt => Some (up_fold (up_inl up_tt))
                                     | up_inr (up_pair T1 T2) => if (interp_aux d0 T1 f, cstar_i T2) is (Some T',Some T'') then
                                                                 Some ( up_fold (up_inr (up_pair T' T''))) else None
                                     | _ => None
                                     end
                      | _ => None
                      end) T
| guard  d0 =>  match T with
               | up_pair (up_singl a) T0 => if f d0 T0 is Some T' then Some (up_pair (up_singl a) T') else None 
               | _ => None 
               end                                                                                              
| _ => if interp_base d is Some f then Some (f T) else None
end.


Definition eRel (a' a : upTree) := event_count a' < event_count a.

Definition not_plus (T : upTree ) :=  match T with | up_inl _ | up_inr _ => false | _ => true end.
Definition not_pair (T : upTree ) :=  match T with | up_pair _ _ => false | _ => true end.
Definition not_star_rule (T : upTree ) :=  match T with |  (up_fold (up_inl up_tt)) | (up_fold (up_inr (up_pair _ _))) => false | _ => true end.
Definition not_guard (T : upTree) := match T with | up_pair (up_singl _) _ => false | _ => true end.

Inductive G_interp : dsl -> upTree -> upTree -> Prop := 
| G_base d f T : interp_base (full_unf d) = Some f -> G_interp d T (f T)
| G_trans  d d0 d1 T T' T'' : full_unf d = (ctrans d0 d1) -> G_interp d0 T T'' -> G_interp d1 T'' T' -> G_interp d T T'
| G_plus_l d d0 d1 T T' : full_unf d =  (cplus d0 d1) ->  G_interp d0 T T'  -> G_interp d (up_inl T) (up_inl T')
| G_plus_r d d0 d1 T T' : full_unf d = (cplus d0 d1) -> G_interp d1 T T'  -> G_interp d (up_inr T) (up_inr T')
| G_plus_bot d d0 d1 T : full_unf d = (cplus d0 d1) -> not_plus T ->   G_interp d T up_bot
| G_seq d d0 d1 T0 T1 T0' T1' : full_unf d =  (cseq d0 d1) -> G_interp d0 T0 T0' -> 
                              G_interp d1 T1 T1' -> G_interp d (up_pair T0 T1) (up_pair T0' T1')
| G_seq_bot d d0 d1 T : full_unf d =  (cseq d0 d1) -> not_pair T -> G_interp d  T up_bot

| G_star0 d' d : full_unf d' =(cstar d) ->  G_interp d' (up_fold (up_inl up_tt)) (up_fold (up_inl up_tt))

| G_star1 d' d T1 T1' T2 T2' : full_unf d' =  (cstar d) -> G_interp d T1 T1' -> G_interp (cstar d) T2 T2' ->
              G_interp d' (up_fold (up_inr (up_pair T1 T2)))  (up_fold (up_inr (up_pair T1' T2')))
| G_star_bot d' d T : full_unf d' =(cstar d) -> not_star_rule T ->  G_interp d' T up_bot
| G_guard d' d T T' a : full_unf d' = guard d -> G_interp d T T' -> G_interp d' (up_pair (up_singl a) T) (up_pair (up_singl a) T')
| G_guard_bot d' d T  : full_unf d' = guard d -> not_guard T ->  G_interp d' T up_bot.
(*| G_fix_bot d' d T  : full_unf d' = cfix d ->  G_interp d' T up_bot.*)

Hint Constructors G_interp.

Lemma G_interp_unf d p p' : G_interp d p p' -> G_interp (full_unf d) p p'.
Proof.
elim=>//=;eauto;intros.
- apply/G_base. rewrite full_unf_idemp. eauto.
- apply/G_trans.  rewrite full_unf_idemp. eauto. eauto. done. 
- apply/G_plus_l. rewrite full_unf_idemp //.  eauto. done.
- apply/G_plus_r. rewrite full_unf_idemp. eauto. done.
- apply/G_plus_bot. rewrite full_unf_idemp. eauto. done.
- apply/G_seq. rewrite full_unf_idemp. eauto. done. done.
- apply/G_seq_bot. rewrite full_unf_idemp. eauto. done.
- apply/G_star0. rewrite full_unf_idemp. eauto. 
- apply/G_star1. rewrite full_unf_idemp. eauto.  done. done.
- apply/G_star_bot. rewrite full_unf_idemp. eauto.  done. 
- apply/G_guard. rewrite full_unf_idemp. eauto.  done. 
- apply/G_guard_bot. rewrite full_unf_idemp. eauto.  done. 
Qed.
(*Inductive D_dom : dsl -> upTree -> Prop := 
| D_trans d0 d1 T :  D_dom d0  T -> (forall T', G_interp d0 T T' ->  D_dom d1 T') -> D_dom  (ctrans d0 d1) T
| D_plus_l d0 d1 T :  D_dom d0 T  -> D_dom  (cplus d0 d1)  (up_inl T)
| D_plus_r d0 d1 T :  D_dom d1 T  -> D_dom  (cplus d0 d1) (up_inr T)
| D_seq d0 d1 T0 T1 :  D_dom d0 T0 -> D_dom d1 T1  -> D_dom (cseq d0 d1) (up_pair T0 T1)
| D_star0 d :  D_dom  (cstar d) (up_fold (up_inl up_tt))
| D_star1 d T1 T2 :  D_dom d T1 -> D_dom (cstar d) T2 ->
              D_dom  (cstar d) (up_fold (up_inr (up_pair T1 T2)))
| D_guard d T a : D_dom d T -> D_dom (guard d) (up_pair (up_singl a) T).*)


Inductive D_dom : dsl -> upTree -> Prop := 
| D_base d f T : interp_base (full_unf d) = Some f -> D_dom d T
| D_trans d d0 d1 T : full_unf d = ctrans d0 d1 -> 
                    D_dom d0  T -> (forall T', G_interp d0 T T' ->  D_dom d1 T') -> D_dom d T
(*| D_trans d d0 d1 T : full_unf d = ctrans d0 d1 -> 
                    D_dom d0  T -> (forall T',  D_dom d1 T') -> D_dom d T*)
| D_plus_l d d0 d1 T : full_unf d = (cplus d0 d1) ->  D_dom d0 T  -> D_dom  d (up_inl T)
| D_plus_r d d0 d1 T : full_unf d = (cplus d0 d1)  -> D_dom d1 T  -> D_dom d (up_inr T)
| D_plus_bot d d0 d1 T : full_unf d = (cplus d0 d1) -> not_plus T ->   D_dom d T

| D_seq d d0 d1 T0 T1 : full_unf d = (cseq d0 d1) ->  D_dom d0 T0 -> D_dom d1 T1  -> D_dom d (up_pair T0 T1)
| D_seq_bot d d0 d1 T : full_unf d =  (cseq d0 d1) -> not_pair T -> D_dom d T

| D_star0 d' d : full_unf d' = cstar d ->  D_dom d' (up_fold (up_inl up_tt))
| D_star1 d' d T1 T2 : full_unf d' =  (cstar d) -> D_dom d T1 -> D_dom (cstar d) T2 ->
              D_dom d' (up_fold (up_inr (up_pair T1 T2)))
| D_star_bot d' d T : full_unf d' =(cstar d) -> not_star_rule T ->  D_dom d' T
| D_guard d' d T a : full_unf d' =  (guard d) ->  D_dom d T -> D_dom d' (up_pair (up_singl a) T)
| D_guard_bot d' d T  : full_unf d' = guard d -> not_guard T ->  D_dom d' T.
(*| D_fix_bot d' d T  : full_unf d' = cfix d ->  D_dom d' T.*)

Hint Constructors D_dom.


Lemma D_dom_unf d p : D_dom d p -> D_dom (full_unf d) p.
Proof.
elim=>//=;eauto;intros.
- apply/D_base. rewrite full_unf_idemp. eauto.
- apply/D_trans.  rewrite full_unf_idemp. eauto. done. eauto.
- apply/D_plus_l. rewrite full_unf_idemp. eauto. done.
- apply/D_plus_r. rewrite full_unf_idemp. eauto. done.
- apply/D_plus_bot. rewrite full_unf_idemp. eauto. done.
- apply/D_seq. rewrite full_unf_idemp. eauto. done. done.
- apply/D_seq_bot. rewrite full_unf_idemp. eauto. done.
- apply/D_star0. rewrite full_unf_idemp. eauto. 
- apply/D_star1. rewrite full_unf_idemp. eauto.  done. done.
- apply/D_star_bot. rewrite full_unf_idemp. eauto.  done. 
- apply/D_guard. rewrite full_unf_idemp. eauto.  done. 
- apply/D_guard_bot. rewrite full_unf_idemp. eauto.  done. 
Qed.

  
Definition proj_trans0  d d0 d1 T (Heq : full_unf d = ctrans d0 d1) (D : D_dom d T) : D_dom d0 T.
Proof. refine(
match D in D_dom d' T' return full_unf d' = ctrans d0 d1 -> D_dom d0 T' with 
| D_trans _ _ _ _ Heq' D' _ => fun HQ => _
| _ => fun HQ => _
end Heq).
rewrite HQ in e. inv e.
rewrite Heq' in HQ. inversion HQ. subst. apply: D'. (*structurally smaller*)
all : try solve [rewrite e in HQ; inv HQ].
Defined.

Definition proj_trans1  d d0 d1 T T' (Heq : full_unf d = ctrans d0 d1) (D : D_dom d T) (H : G_interp d0 T T') : 
  D_dom d1 T'.
Proof. refine(
match D in D_dom d' T return full_unf d' = ctrans d0 d1 -> G_interp d0 T T' -> D_dom d1 T' with 
| D_trans _ _ _ _ Heq' D' _ => fun HQ HG => _
| _ => fun HQ HG => _
end Heq H).
all : try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e. inv e.
rewrite Heq' in HQ. inv HQ. apply/d5. done.
Defined.

Definition proj_inl  d d0 d1 T' T (Heq : full_unf d = cplus d0 d1) (Heq2 : T' = up_inl T) (D : D_dom d T') : D_dom d0 T.
Proof. refine(
match D in D_dom d' T' return  full_unf d' = cplus d0 d1 -> T' = up_inl T  ->  D_dom d0 T with 
| D_plus_l _ _ _ _ Heq' D' => fun HQ TQ => _
| _ => fun HQ TQ => _
end  Heq Heq2). 
all : try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e. inv e.
rewrite HQ in Heq'. inv Heq'.  inv TQ.
Defined.

Definition proj_inr  d d0 d1 T' T (Heq : full_unf d = cplus d0 d1) (Heq2 : T' = up_inr T) (D : D_dom d T') : D_dom d1 T.
Proof. refine(
match D in D_dom d' T' return  full_unf d' = cplus d0 d1 -> T' = up_inr T  ->  D_dom d1 T with 
| D_plus_l _ _ _ _ Heq' D' => fun HQ TQ => _
| _ => fun HQ TQ => _
end  Heq Heq2). 
all : try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e. inv e.
rewrite HQ in Heq'. inv Heq'.  inv TQ.
rewrite e in HQ. inv HQ.
Defined.

Definition proj_seq1  d d0 d1 T' T0 T1 (Heq : full_unf d = cseq d0 d1) (Heq2 : T' = up_pair T0 T1) (D : D_dom d T') : D_dom d0 T0.
Proof. refine(
match D in D_dom d' T' return  full_unf d' = cseq d0 d1 -> T' = up_pair T0 T1  ->  D_dom d0 T0 with 
| D_plus_l _ _ _ _ Heq' D' => fun HQ TQ => _
| _ => fun HQ TQ => _
end  Heq Heq2). 
all : try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e. inv e.
rewrite HQ in Heq'. inv Heq'.  inv TQ.
rewrite e in HQ. inv HQ.
Defined.

Definition proj_seq2  d d0 d1 T' T0 T1 (Heq : full_unf d = cseq d0 d1) (Heq2 : T' = up_pair T0 T1) (D : D_dom d T') : D_dom d1 T1.
Proof. refine(
match D in D_dom d' T' return  full_unf d' = cseq d0 d1 -> T' = up_pair T0 T1  ->  D_dom d1 T1 with 
| D_plus_l _ _ _ _ Heq' D' => fun HQ TQ => _
| _ => fun HQ TQ => _
end  Heq Heq2). 
all : try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e. inv e.
rewrite HQ in Heq'. inv Heq'.  inv TQ.
rewrite e in HQ. inv HQ.
Defined.

Definition proj_cstar1  d d0 T' T0 T1 T2 (Heq : full_unf d = cstar d0) (Heq2 : T' = up_fold T0) (Heq3 : T0  = up_inr (up_pair T1 T2)) (D : D_dom d T') : D_dom d0 T1.
Proof. refine(
match D in D_dom d' T' return  full_unf d' = cstar  d0 -> T' = up_fold T0 ->  T0 = (up_inr (up_pair T1 T2))  ->  D_dom d0 T1 with 
| D_plus_l _ _ _ _ Heq' D' => fun HQ TQ => _
| _ => fun HQ TQ => _
end  Heq Heq2 Heq3).
all : try solve [rewrite e in HQ; inv HQ].
all: subst.
rewrite HQ in e. inv e.
rewrite HQ in Heq'. inv Heq'.  inv TQ.
rewrite e in HQ. inv HQ.
Defined.

(*Lemma proj_trans0 : forall d d0 d1 T, full_unf d = ctrans d0 d1 -> D_dom d T -> D_dom d0 T.
Proof.
intros. inv H0. rewrite H in H1. inversion H1. subst.
inv H1. 

 := *)
(*match H with 
| D_trans _ _ _ _ Heq Hd Hd' => *)

(*Need to define output with conformity to build third premise of D_trans*)

Definition proj1 {A : Type} (P : A -> Prop) (x : A) (H : {x: A | P x}) : A := 
match H with 
| exist x' _ => x' 
end.

(*Definition cplus_i (T : upTree) : {T' | G_interp d T T'} := 
match T as T' in T = T' -> _  with 
| up_inl T0 => *)



(*Fixpoint interp (r0 r1 : regex) (d : dsl) (T : upTree)  (HI : INEQ r0 r1 d) (HT : typing T r0) {struct T} :  { T' | G_interp d T T' /\ typing T r1}.*)

(*Lemma D_dom_not_fix : forall d d0 T, full_unf d = cfix d0 -> ~D_dom d T.
Proof.
intros. intro. inv H0;subst. all: try solve [rewrite H // in H1]. 
Qed.*)


Fixpoint repeat_int (d : dsl) (T : upTree) (D : D_dom d) := 
interp d T (repeat_int 

Fixpoint interp d (T : upTree) {struct T} :  upTree.
Proof. refine (
match full_unf d as d' return  full_unf d = d' -> { T' | G_interp d T T'}  with 
| ctrans d0 d1 => fun Heq => match interp d0 T (proj_trans0 Heq D) with 
                          | exist T'' _ => exist (interp d1 T'' (proj_trans1 Heq D)) _
                         end 
| cplus d0 d1 => fun Heq => (match T as T' return T = T' ->  { T' | G_interp d T T'}  with 
                           | up_inl T0 => fun HT => exist (up_inl (interp d0 T0 _)) _
                           | up_inr T1 => fun HT => exist (up_inr (interp d1 T1 _)) _ 
                           | _ => fun _ => T 
                         end) Logic.eq_refl
| cseq  d0 d1  => fun Heq => match T with up_pair T0 T1 => up_pair (interp d0 T0 _) (interp d1 T1 _) | _ => T end 
| cstar d0 => fun Heq  => (fix cstar_i T' := 
                      match T' with 
                      | up_fold T0 => match T0 with 
                                     | up_inl up_tt => up_fold (up_inl up_tt)
                                     | up_inr (up_pair T1 T2) => up_fold (up_inr (up_pair (interp d0 T1 _) 
                                                                                         (cstar_i T2)))
                                     | _ => up_bot 
                                     end
                      | _ => up_bot
                      end) T
| guard  d0 =>

 fun D  => guard_i (fun T => interp d0 T _) T
| _ => fun D => if interp_base d is Some f then f T else T
end D Logic.eq_refl).
move: (D_dom_unf D). rewrite Heq. move=>HH. inv HH. inv H. apply/H1.
apply/
 intros. inv 
admit.
subst.
move/D_dom_unf: D. rewrite Heq. intros. inv D. inv H0.


Fixpoint interp d (T : upTree) (D: D_dom d T) {struct D} : { T' | G_interp d T T'}.
Proof. refine (
match full_unf d as d' return D_dom d T -> full_unf d = d' -> { T' | G_interp d T T'}   with 
| ctrans d0 d1 => fun D Heq => match (interp d0 T (proj_trans0 Heq D)) with 
                             | exist T'' _ => match interp d1 T'' (proj_trans1 Heq D _) with 
                                               | exist T''' _ => exist _ T''' _
                                             end
                            end
| cplus d0 d1 => fun D Heq => (match T as T' return T = T' -> { T'' | G_interp d T T''}  with 
                           | up_inl T0 => fun HT => match interp d0 T0 (proj_inl Heq HT D) with 
                                                  | exist T0' _ =>  exist _ (up_inl T0') _ 
                                                end
                           |  up_inr T1 => fun HT => match interp d1 T1 (proj_inr Heq HT D) with 
                                                  | exist T1' _ => exist _ (up_inr T1') _ 
                                                 end
                           | _ => fun HT => exist _ up_bot _ end) Logic.eq_refl
| cseq  d0 d1  => fun D Heq => (match T as T' return T = T' ->  { T'' | G_interp d T T''}  with 
                             | up_pair T0 T1 => fun HT => match (interp d0 T0 (proj_seq1 Heq HT D)),(interp d1 T1 (proj_seq2 Heq HT D)) with 
                                                 | exist T0' _ ,exist T1' _ =>   exist _ (up_pair T0' T1') _
                                                end
                             | _ => fun HT => exist _ up_bot _ end) Logic.eq_refl
| cstar d0 => fun D Heq  => let T0 := (
                      (fix cstar_i (T' : upTree) (D' : D_dom d T') {struct T'} := 
                      (match T' as T'' return T' = T'' ->  { T''' | G_interp d T' T'''}  with 
                      | up_fold T0 => fun HT => 
                                     (match T0 as T0' return T0 = T0' ->  { T''' | G_interp d T' T'''}  with 
                                     | up_inl up_tt => fun HT' => exist _ (up_fold (up_inl up_tt)) _
                                     | up_inr (up_pair T1 T2) => fun HT' => match (interp d0 T1 (proj_cstar1 Heq HT HT' D)), (cstar_i T2 _) with 
                                                                          | exist T'' _, exist T2' _ => exist _ (up_fold (up_inr (up_pair T'' T2'))) (_)
                                                                        end
                                     | _ => fun HT' => exist _ up_bot _
                                     end) Logic.eq_refl
                      | _ => fun HT => exist _ up_bot _
                      end) Logic.eq_refl ) T _)
                      in match T0  with 
                          | exist T' _ => exist _ T' _
                         end
| guard  d0 => fun D Heq  => match T as T' return T = T' -> { T'' | G_interp d T T'' } with
                          | up_pair (up_singl a) T0 => fun HT => match interp d0 T0 _ with 
                                                             | exist T1 _ => exist _ (up_pair (up_singl a) T1) _ 
                                                             end 
                          | _ => fun HT => exist _ up_bot _ 
                         end Logic.eq_refl
| _ => fun D Heq => match interp_base (full_unf d) as d' return interp_base (full_unf d) = d' ->  { T'' | G_interp d T T'' } with
                 |  Some f => fun HT => exist _ (f T) _ 
                 |  _ => fun HT => exist _ up_bot _
                end Logic.eq_refl
end D Logic.eq_refl).
all: try solve [ subst;eauto |
                 move: (D_dom_unf D);  rewrite Heq; move=>HH; inv HH | 
                con; rewrite Heq; rewrite Heq in HT; done |
                rewrite Heq //= in HT].
(*- move: (D_dom_unf D). rewrite Heq. move=> HH. inv HH. inv H.
  apply/H1. done. *)

(*- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H0. Guarded.
- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H0.
- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H1.
- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H1.*)

(*- inv g. inv H. apply/G_star0. eauto. inv H.
  apply/G_star1. eauto. done. done.
  inv H. apply/G_star_bot. eauto. done.*) 
- move: (D_dom_not_fix Heq D)=>//. Guarded.
- subst. inv D. all: try solve[ rewrite Heq // in H].
  rewrite Heq in H1. ssa. rewrite Heq in H2. inv H2. 
Unshelve.
(*apply/G_star_bot *)
all: try solve [subst; eauto]. 
rewrite HT' in HT. 
- move: (D_dom_unf D). rewrite Heq. move=> HH.   subst. inv D'. inv H1. Guarded.
- subst.  inv D'.   inv H1.
- subst. apply/G_star1. eauto. done.  simpl in y.
- move: (G_interp_unf y). rewrite Heq. move=> HH. done.   
- move: (D_dom_unf D). rewrite Heq. done.
Qed.





Fixpoint interp d (T : upTree) (D: D_dom d T) {struct D} : { T' | G_interp d T T'}.
Proof. refine (
match full_unf d as d' return D_dom d T -> full_unf d = d' -> { T' | G_interp d T T'}   with 
| ctrans d0 d1 => fun D Heq => match (interp d0 T (proj_trans0 Heq D)) with 
                             | exist T'' _ => match interp d1 T'' (proj_trans1 Heq D _) with 
                                               | exist T''' _ => exist _ T''' _
                                             end
                            end
| cplus d0 d1 => fun D Heq => (match T as T' return T = T' -> { T'' | G_interp d T T''}  with 
                           | up_inl T0 => fun HT => match interp d0 T0 (proj_inl Heq HT D) with 
                                                  | exist T0' _ =>  exist _ (up_inl T0') _ 
                                                end
                           |  up_inr T1 => fun HT => match interp d1 T1 (proj_inr Heq HT D) with 
                                                  | exist T1' _ => exist _ (up_inr T1') _ 
                                                 end
                           | _ => fun HT => exist _ up_bot _ end) Logic.eq_refl
| cseq  d0 d1  => fun D Heq => (match T as T' return T = T' ->  { T'' | G_interp d T T''}  with 
                             | up_pair T0 T1 => fun HT => match (interp d0 T0 (proj_seq1 Heq HT D)),(interp d1 T1 (proj_seq2 Heq HT D)) with 
                                                 | exist T0' _ ,exist T1' _ =>   exist _ (up_pair T0' T1') _
                                                end
                             | _ => fun HT => exist _ up_bot _ end) Logic.eq_refl
| cstar d0 => fun D Heq  => let T0 := (
                      (fix cstar_i (T' : upTree) (D' : D_dom d T') {struct T'} := 
                      (match T' as T'' return T' = T'' ->  { T''' | G_interp d T' T'''}  with 
                      | up_fold T0 => fun HT => 
                                     (match T0 as T0' return T0 = T0' ->  { T''' | G_interp d T' T'''}  with 
                                     | up_inl up_tt => fun HT' => exist _ (up_fold (up_inl up_tt)) _
                                     | up_inr (up_pair T1 T2) => fun HT' => match (interp d0 T1 (proj_cstar1 Heq HT HT' D')), (cstar_i T2 _) with 
                                                                          | exist T'' _, exist T2' _ => exist _ (up_fold (up_inr (up_pair T'' T2'))) (_)
                                                                        end
                                     | _ => fun HT' => exist _ up_bot _
                                     end) Logic.eq_refl
                      | _ => fun HT => exist _ up_bot _
                      end) Logic.eq_refl ) T _)
                      in match T0  with 
                          | exist T' _ => exist _ T' _
                         end
| guard  d0 => fun D Heq  => match T as T' return T = T' -> { T'' | G_interp d T T'' } with
                          | up_pair (up_singl a) T0 => fun HT => match interp d0 T0 _ with 
                                                             | exist T1 _ => exist _ (up_pair (up_singl a) T1) _ 
                                                             end 
                          | _ => fun HT => exist _ up_bot _ 
                         end Logic.eq_refl
| _ => fun D Heq => match interp_base (full_unf d) as d' return interp_base (full_unf d) = d' ->  { T'' | G_interp d T T'' } with
                 |  Some f => fun HT => exist _ (f T) _ 
                 |  _ => fun HT => exist _ up_bot _
                end Logic.eq_refl
end D Logic.eq_refl).
all: try solve [ subst;eauto |
                 move: (D_dom_unf D);  rewrite Heq; move=>HH; inv HH | 
                con; rewrite Heq; rewrite Heq in HT; done |
                rewrite Heq //= in HT].
(*- move: (D_dom_unf D). rewrite Heq. move=> HH. inv HH. inv H.
  apply/H1. done. *)

(*- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H0. Guarded.
- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H0.
- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H1.
- subst. move: (D_dom_unf D). rewrite Heq=>HH. inv HH. inv H1.*)

(*- inv g. inv H. apply/G_star0. eauto. inv H.
  apply/G_star1. eauto. done. done.
  inv H. apply/G_star_bot. eauto. done.*) 
- move: (D_dom_not_fix Heq D)=>//. Guarded.
- subst. inv D. all: try solve[ rewrite Heq // in H].
  rewrite Heq in H1. ssa. rewrite Heq in H2. inv H2. 
Unshelve.
(*apply/G_star_bot *)
all: try solve [subst; eauto]. 
rewrite HT' in HT. 
- move: (D_dom_unf D). rewrite Heq. move=> HH.   subst. inv D'. inv H1. Guarded.
- subst.  inv D'.   inv H1.
- subst. apply/G_star1. eauto. done.  simpl in y.
- move: (G_interp_unf y). rewrite Heq. move=> HH. done.   
- move: (D_dom_unf D). rewrite Heq. done.
Qed.





(*Definition guard_i (f : fType) : fType := 
fun T => 
match T with 
| up_pair (up_singl a) T' => up_pair (up_singl a) (f T') 
| _ => up_bot 
end.*)


Fixpoint interp d (T : upTree) : upTree.
Proof. refine (
match full_unf d as d' return  full_unf d = d' -> { T' | G_interp d T T'}  with 
| ctrans d0 d1 => fun Heq => match interp d0 T (proj_trans0 Heq D) with 
                          | exist T'' _ => exist (interp d1 T'' (proj_trans1 Heq D)) _
                         end 
| cplus d0 d1 => fun Heq => (match T as T' return T = T' ->  { T' | G_interp d T T'}  with 
                           | up_inl T0 => fun HT => exist (up_inl (interp d0 T0 _)) _
                           | up_inr T1 => fun HT => exist (up_inr (interp d1 T1 _)) _ 
                           | _ => fun _ => T 
                         end) Logic.eq_refl
| cseq  d0 d1  => fun Heq => match T with up_pair T0 T1 => up_pair (interp d0 T0 _) (interp d1 T1 _) | _ => T end 
| cstar d0 => fun Heq  => (fix cstar_i T' := 
                      match T' with 
                      | up_fold T0 => match T0 with 
                                     | up_inl up_tt => up_fold (up_inl up_tt)
                                     | up_inr (up_pair T1 T2) => up_fold (up_inr (up_pair (interp d0 T1 _) 
                                                                                         (cstar_i T2)))
                                     | _ => up_bot 
                                     end
                      | _ => up_bot
                      end) T
| guard  d0 => fun D  => guard_i (fun T => interp d0 T _) T
| _ => fun D => if interp_base d is Some f then f T else T
end D Logic.eq_refl).
move: (D_dom_unf D). rewrite Heq. move=>HH. inv HH. inv H. apply/H1.
apply/
 intros. inv 
admit.
subst.
move/D_dom_unf: D. rewrite Heq. intros. inv D. inv H0.

admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.


 admit.
apply: D_trans. 
admit.
eauto.






Definition cstar_i (f : fType) : fType := 

Lemma cstar_i_t : forall A B f, A <T= B ~> f -> (Star A)  <T= (Star B) ~> (cstar_i f).
Proof.
move=> r r' f Hf T. move Heq: (upTree_size T) => n. move: Heq. suff: upTree_size T <= n -> typing T (Star r) -> typing (cstar_i f T) (Star r').
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq  r r' Hf. elim=>//=.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 r1 Himp Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. con. con. con. apply/Himp. done. apply/IH. ssa. lia. eauto. 
done.
Qed.

(*Fixpoint interp_aux (r0 r1 : regex)
           (d : dsl dsl_co r0 r1)  (f : forall x y, dsl_co x y -> fType ) :  fType :=
match d with 
| shuffle _ _ _ => shuffle_i
| shuffleinv _ _ _ => shuffleinv_i


| retag _ _ => retag_i
| untagL _ => untagL_i
| untagLinv _=> untagLinv_i
| untag _=> untag_i
| tagL _ _=> tagL_i

| assoc _ _ _ => assoc_i
| associnv _ _ _ => associnv_i

| swap _ =>  swap_i
| swapinv _ => swapinv_i

| proj _ => proj_i
| projinv _ => projinv_i

| abortR _ => abortR_i
| abortRinv _ => abortRinv_i

| abortL _ => abortL_i
| abortLinv _=> abortLinv_i

| distL _ _ _ => distL_i
| distLinv _ _ _ => distLinv_i

| distR _ _ _ => distR_i
| distRinv _ _ _ => distRinv_i

| wrap _ => wrap_i
| wrapinv _ => wrapinv_i

| drop _ => drop_i 
| dropinv _ => dropinv_i
| cid _=> cid_i

| ctrans _ _ _ d0 d1 => ctrans_i (interp_aux d0 f) (interp_aux d1 f)
| cplus _ _ _ _ d0 d1 => cplus_i (interp_aux d0 f) (interp_aux d1 f)

| cseq _ _ _ _ d0 d1  => cseq_i (interp_aux d0 f) (interp_aux d1 f)
| cstar _ _ d0 => cstar_i (interp_aux d0 f)
(*| rule_cfix r r' (p  : dsl R dsl) : dsl R r  r' ~> p[d (cfix p) .: dsl R var_dsl] ->  r  r' ~> (cfix p) (*guarded p otherwise unsound*)*)
| guard _ _ _ pco => guard_i (f _ _ pco)
(*| _ => fun _ => up_bot*)
end.
*)


(*Fixpoint interp (r0 r1 : regex)
           (d : dsl2 dsl_co r0 r1)  (f : forall x y, dsl_co x y -> x <O= y ) :  r0 <O= r1 :=
match d in dsl2 _ r0 r1 return (pTree r0) -> option (pTree r1) with 
| @cid2 _ A => (@cid_o A)
| @shuffle2 _ A B C => (@shuffle_o A B C)
| @shuffleinv2 _ A B C => (@shuffleinv_o A B C)
| @ctrans2 _ A B C d0 d1 => (@ctrans_o A B C) (@interp _ _ d0 f) (@interp _ _ d1 f)
| @cplus2 _ A B C D d0 d1 => (@cplus_o A B C D (@interp _ _ d0 f)) (@interp _ _ d1 f)
| @guard2 _ a A B pco => guard_o (f _ _ pco)
end.*)

Fixpoint interp_n (n : nat) (r0 r1 : regex) (d : dsl_co r0 r1) : fType :=
match d with 
| Co_build _ _ dco => if n is n'.+1 then interp_aux dco (@interp_n n') else fun _ => up_bot
end. 




(*Lemma interp_aux_le : forall r r' (d: dsl dsl_co r r') (f : forall x y, dsl_co x y -> fType) T, 
(forall x y (d : dsl_co x y) T, upTree_size (f _ _ d T) <= upTree_size T) ->  upTree_size (interp_aux d f T) <= upTree_size T.
Proof.
move=> r r' d f T.
destruct T;ssa.
destruct d;ssa.

elim: d T=>//=;intros. case: T=>//. move=>u. simpl. destruct u;ssa.
simpl.
 elim=>//.
*)
(*Lemma interp_aux_ext : forall r0 r1 (d : dsl dsl_co r0 r1) (f f' : forall x y, dsl_co x y -> fType) n T, upTree_size T < n ->
 ( forall T, upTree_size T < n -> forall x y (d : dsl_co x y), f _ _ d = f' _ _ d) -> interp_aux d f T = interp_aux d f' T. 
Proof.
move=> r0 r1. elim=>//.
- move=> A0 B C d IH d0 IH2 f f' n T Hsize Hext.
  rewrite /= /ctrans_i /=. erewrite IH. 2 : eauto. apply/IH2.*)


(*Lemma interp_n_unf : forall i n r0 r1 (d : dsl_co r0 r1) T, upTree_size T < n -> interp_n n d T = interp_n (i + n) d T. 
Proof.
elim=>//.
move=> n IH n0 r0 r1 d T Hsize /=. destruct d. 
destruct n0. move:(upTree_size1 T). lia.
simpl. destruct d=>//.
rewrite /= /ctrans_i /=. rewrite -IH.
f_equal.
rewrite -IH.
f_equal. 
rewrite IH //=.
rewrite /interp_aux.
*)
Definition interp (r0 r1 : regex) (d : dsl_co r0 r1) : fType := fun T => interp_n (upTree_size T) d T.

(*Require Import Coq.Program.Equality.*)
Lemma interp_n_unf_typing : forall r0 r1 (d : dsl dsl_co r0 r1) T (f : forall x y (d' : dsl_co x y), fType), 
(forall x y (d' : dsl_co x y) T', typing T' x -> typing (f _ _ d' T') y)  ->  typing T r0 -> typing (interp_aux d f T) r1. 
Proof.
move=> r0 r1. elim=>//;eauto.
intros. inve H2. simpl.  eauto.  simpl.  eauto. 
intros. inve H2. simpl.  eauto. 
intros. inve H1. simpl. inve H2. inve H1. inve H1. con. con. con. eauto. eauto.
intros. inve H0. simpl. inve H1. 
Qed.

(*Lemma interp_aux_cstar : forall T r0 r1 (d : dsl dsl_co r0 r1) (f f' : forall x y (d' : dsl_co x y), fType), typing T r0 ->  
(forall x y (d' : dsl dsl_co x y) T', typing T' x -> interp_aux d' f T' = interp_aux d' f' T') ->  
(forall x y (d' : dsl_co x y) T', typing T' x -> typing (f _ _ d' T') y) ->
interp_aux (cstar d) f T = interp_aux (cstar d) f' T.
Proof.
move=> T. move Heq: (upTree_size T)=>n. move: Heq.
suff:  upTree_size T <= n ->
  forall (r0 r1 : regex) (d : dsl dsl_co r0 r1)
    (f f' : forall x y : regex, dsl_co x y -> fType),
  typing T r0 ->
 (forall (x y : regex) (d' : dsl dsl_co x y) (T' : upTree), typing T' x -> interp_aux d' f T' = interp_aux d' f' T') ->
  (forall (x y : regex) (d' : dsl_co x y), x <T= y ~> f x y d') -> interp_aux (cstar d) f T = interp_aux (cstar d) f' T.
move=>HH H2. intros. apply/HH;eauto. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. 
move=> u Hsize _ r1 r2 d f f' Ht Heq Hf. inv Ht.   inv H0.  inv H2. 

f_equal. f_equal. f_equal. apply/Heq.  done. admit. apply/IH. ssa. lia. done. eauto. eauto. eauto.
admit. apply/IH. apply/IH;eauto. ssa. lia.
lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. inv H4. inv H3. apply/IH. ssa. done.
con. con. con. done. apply/IH. ssa. lia. done.
Qed.*)

(*Lemma interp_aux_cstar : forall T r0 r1 (d : dsl dsl_co r0 r1) (f f' : forall x y (d' : dsl_co x y), fType), typing T r0 ->  
(forall T, typing T d ->  interp_aux d f T = interp_aux d f' T) -> 
interp_aux (cstar d) f T = interp_aux (cstar d) f' T.
Proof.
move=> T. move Heq: (upTree_size T)=>n. move: Heq.
suff:  upTree_size T <= n ->
  forall (r0 r1 : regex) (d : dsl dsl_co r0 r1)
    (f f' : forall x y : regex, dsl_co x y -> fType),
  typing T r0 ->
  interp_aux (cstar d) f T = interp_aux (cstar d) f' T.
move=>HH H2. intros. apply/HH;eauto. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. 
move=> u Hsize _ r1 r2 d f f' Ht. inv Ht.   inv H0.  inv H2. 

f_equal. f_equal. f_equal. admit. apply/IH. ssa. lia. done. eauto. eauto. eauto.
admit. apply/IH. apply/IH;eauto. ssa. lia.
lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. inv H4. inv H3. apply/IH. ssa. done.
con. con. con. done. apply/IH. ssa. lia. done.
Qed.


elim: n Heq=>//.




Lemma interp_aux_cstar : forall T r0 r1 (d : dsl dsl_co r0 r1) (f f' : forall x y (d' : dsl_co x y), fType), typing T r0 ->  
(forall x y (d' : dsl_co x y) T', typing T' x -> f _ _ d' T' = f' _ _ d' T') ->  
(forall x y (d' : dsl_co x y) T', typing T' x -> typing (f _ _ d' T') y) ->
interp_aux (cstar d) f T = interp_aux (cstar d) f' T.
Proof.
move=> T. move Heq: (upTree_size T)=>n. move: Heq.
suff:  upTree_size T <= n ->
  forall (r0 r1 : regex) (d : dsl dsl_co r0 r1)
    (f f' : forall x y : regex, dsl_co x y -> fType),
  typing T r0 ->
  (forall (x y : regex) (d' : dsl_co x y) (T' : upTree),
   typing T' x -> f x y d' T' = f' x y d' T') ->
  (forall (x y : regex) (d' : dsl_co x y), x <T= y ~> f x y d') ->
  interp_aux (cstar d) f T = interp_aux (cstar d) f' T.
move=>HH H2. intros. apply/HH;eauto. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. 
move=> u Hsize _ r1 r2 d f f' Ht Heq Hf. inv Ht.   inv H0.  inv H2. 

f_equal. f_equal. f_equal. admit. apply/IH. ssa. lia. done. eauto. eauto. eauto.
admit. apply/IH. apply/IH;eauto. ssa. lia.
lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. inv H4. inv H3. apply/IH. ssa. done.
con. con. con. done. apply/IH. ssa. lia. done.
Qed.


elim: n Heq=>//.
*)
Lemma interp_n_unf : forall r0 r1 (d : dsl dsl_co r0 r1) T (f f' : forall x y (d' : dsl_co x y), fType), typing T r0 -> 
(forall x y (d' : dsl_co x y) T', typing T' x -> f _ _ d' T' = f' _ _ d' T') ->  
(forall x y (d' : dsl_co x y) T', typing T' x -> typing (f _ _ d' T') y) ->
interp_aux d f T = interp_aux d f' T. 
Proof.
move=> r0 r1. elim=>//.
intros. rewrite /= /ctrans_i /=. erewrite H;eauto. apply/H0;eauto.
erewrite <- H;eauto. apply/interp_n_unf_typing. eauto. done.
intros. rewrite /=. rewrite /cplus_i. inve H1. f_equal. eauto. f_equal. eauto.
intros. rewrite /= /cseq_i /=. inve H1. f_equal. eauto. eauto.
intros. rewrite /=. inve H0. inv H3. inv H5.
elim: d H;ssa.
/cstar_i /=.
destruct T;ssa. f_equal. apply/H. done.
erewrite H0.
intros.
eauto.
move=> r0 r1 d T f f' Ht.
elim: Ht d=>//=.
- move=> d Hf. dependent induction d;ssa.
  rewrite /ctrans_i /=.
dependent destruction d.
 inv d.

Lemma interpP : forall r0 r1 (d : dsl_co r0 r1) T, upTree_size T < n -> typing T r0 -> typing (interp_n n d T) r1. 


Lemma interpP : forall r0 r1 (d : dsl_co r0 r1) T, typing T r0 -> typing (interp d T) r1 /\ uflatten T = (uflatten (interp d T)).
Proof. Admitted.

(*Lemma interp_uflatten : forall r0 r1 (d : dsl_co r0 r1) T, typing T r0 -> typing (interp d T) r1.*)


(*Fixpoint interp_wrap (n : nat) (r0 r1 : regex) (d : dsl_co r0 r1) : r0 <O= r1 :=
match d in dsl_co x y return x <O= y  with 
          | Co_build _ _ dco => if n is n'.+1 then interp dco (interp_wrap n') else fun _ => None
end. *)



(*Lemma fix_eq : forall n, (fix interp_wrap (n0 : fin) (r0 r1 : regex) (d0 : dsl_co r0 r1) {struct n0} : fType := 
match d0 in (dsl_co x y) h
    | @Co_build A1 B0 dco => match n0 with
                            | 0 => fun=> up_bot
                            | n'.+1 => interp dco (@interp_wrap n')
                            end
 end) n = interp_wrap n.
Proof. done. Qed.*)

Lemma interp_wrap_unf : forall n r0 r1 (d : dsl_co r0 r1), interp_wrap n.+1 d = match d  with 
          | Co_build _ _ dco => interp dco (@interp_wrap n) end.
Proof. move => n r0 r1 d //=. Qed.






(*Require Import Coq.Program.Equality.*)
(*Check interp.
Lemma interp_wrap0 : forall r0 r1 (d : dsl2 dsl_co r0 r1), interp d (interp_wrap 0) = fun _ => None.
Proof.
move => r0 r1 d. fext. move=> x. 
elim: d x=>//.
rewrite /interp_wrap. case: d=>//.
Qed.*)

Lemma interp_trans : forall r0 r1 r2  (f : forall x y, dsl_co x y -> fType) (d : dsl dsl_co r0 r1) (d' : dsl dsl_co r1 r2) T, interp (ctrans d d') f T -> interp d f T.
Proof.
move=> r0 r1 r2 f d d' T. rewrite /= /ctrans_o /obind /oapp /=. case: (interp _ _ _)=>//.
Qed.


Lemma interp_trans2 : forall r0 r1 r2  (f : forall x y, dsl_co x y -> x <O= y)  (d : dsl2 dsl_co r0 r1) (d' : dsl2 dsl_co r1 r2) T T', interp (ctrans2 d d') f T -> interp d f T = Some T' -> interp d' f T'.
Proof.
move => r0 r1 r2 Hf d d' T T' /= + Hsome. rewrite /= /ctrans_o /obind /oapp /=. rewrite Hsome //.
Qed.

Lemma pTree_eq : forall (A0 : regex), (fix pTree (r : regex) : Type := match r with
                                           | Eps => unit
                                           | Empt => void
                                           | Event a => {a' : A & a' == a}
                                           | r0 _+_ r1 => (pTree r0 + pTree r1)%type
                                           | r0 _;_ r1 => (pTree r0 * pTree r1)%type
                                           | Star r0 => seq (pTree r0)
                                           end) A0 = pTree A0.
Proof. done. Qed.

Lemma reg_size1 : forall a (T : pTree (Event a)), @reg_size (Event a) T = 1.
Proof.
move=> a T. rewrite /reg_size //.
Qed.

Lemma interp_ineq : forall A B (d : dsl2 dsl_co A B) (T : pTree A) (T' : pTree B) (f : forall x y, dsl_co x y -> x <O= y), (forall x y (dco : dsl_co x y) (T0 : pTree x) (T1 : pTree y) , f x y dco T0 = Some T1 -> reg_size T1 <= reg_size T0) ->  
                                                                                                                    interp d f T = Some T' -> reg_size T' <= reg_size T.
Proof.
move=> A' B d T T' f Hf.  
- elim: d T T'.
 *  move=> B0 T0 T1 /=. rewrite /cid_o. case=>//->//.
 * move => A0 B0 C T T' /=. rewrite /shuffle_o /shuffle_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C T T' /=. rewrite /shuffleinv_o /shuffleinv_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C d IH d0 IH2 T T' Hsome. 
   have: interp (ctrans2 d d0) f T by rewrite Hsome//. 
   move/[dup]=>Tsome. move/interp_trans.
   case Heq: (interp _ _ _)=>// [T''] _. move: (IH _ _ Heq)=>Hsize. 
   move/interp_trans2: (Heq). move/(_ _ d0 Tsome).
   case Heq2: (interp _ _ _)=>// [T'''] _. move: (IH2 _ _ Heq2). 
   move=> Hsize2.
   move: Hsome. rewrite /= /ctrans_o /= /obind /oapp /= Heq Heq2.
   case. move=> HT;subst. lia.
 * move=> A0 B0 C D d IH d0. move=> IH2 T T' /=. rewrite /cplus_o /=. 
   case: T. 
  **  move=> T2. rewrite /omap /obind /oapp. 
      case Heq: (interp _ _ _) => // [T3 ]. case. move=> HT3;subst. apply/IH. eauto. 
  **  move=> T2. rewrite /omap /obind /oapp. 
      case Heq: (interp _ _ _) => // [T3 ]. case. move=> HT3;subst. apply/IH2. eauto. 
 * move => A0 B0 r T T' /= T'0. rewrite /guard_o. destruct T' eqn:Heqn. subst. destruct (f _ _ _ _) eqn:Heqn. case. move=> Ht0;subst. 
   suff: reg_size a1 <= reg_size a0. lia.  eauto. done.
Qed.
Check interp_wrap.
Lemma interp_wrap_ineq : forall n A B (d : dsl_co A B) (T : pTree A) (T' : pTree B),  interp_wrap n d T = Some T' -> reg_size T' <= reg_size T.
Proof.
elim.
- move=> A0 B [] //=.
- move=> n IH A0 B [] T T' d T0 T0'. rewrite interp_wrap_unf. move=> Hint.  apply/interp_ineq;last by eauto. 
  move=> x y dco T1 T2 Hin. eauto.
Qed.


Lemma interp_some : forall A B (f : forall x y, dsl_co x y -> x <O= y) (d : dsl2 dsl_co A B) (T : pTree A) , (forall x y (dco : dsl_co x y) (T0 : pTree x), f x y dco T0) ->  
                                                                                                                    interp d f T.
Proof.
move=> A' B f. 
- elim=>//. 
 * move=> A0 B0 C d IH d0 IH2 T Hf. 
   rewrite /= /ctrans_o /obind /oapp /=.
   move: (@IH T Hf). case Hcase: (interp _ _ _)=>// [T1] _.
   apply/IH2. eauto.
 * move=> A0 B0 C D d IH d0. move=> IH2 T Hf /=. rewrite /cplus_o /=. 
   case: T. 
  **  move=> T2. rewrite /omap /obind /oapp. 
      move: (@IH T2 Hf).
      case Heq: (interp _ _ _) => // [T3 ]. 
  **  move=> T2. rewrite /omap /obind /oapp. 
      move: (@IH2 T2 Hf).
      case Heq: (interp _ _ _) => // [T3 ]. 
 * move => A0 B0 C r T Hf /=. rewrite /guard_o. destruct T eqn:Heqn;subst.
   move: (Hf B0 C r a0). case: (f _ _ _)=>//.
Qed.

Lemma interp_wrap_some : forall n r0 r1 (d : dsl_co r0 r1) (T : pTree r0), reg_size T < n -> interp_wrap n d T.
Proof.
elim.
- move=> r0 r1 d T // Hsize.  
- move => n IH r0 r1 d T Hsize /=. destruct d.
  elim: d T Hsize IH=>//.
 * move=> A1 B0 C d IH d0 IH2 T Hsize IH3 /=. rewrite /ctrans_o /obind /oapp /=.
   have: interp d (interp_wrap n) T;first by eauto. case Hcase: (interp _ _ _)=>// [ T1 ] _.
   apply/IH2.
   have : reg_size T1 <= reg_size T by 
   apply/interp_ineq;last eauto; move=> x y dco T0 T2 Hint; apply/interp_wrap_ineq; eauto.
   move=> Hsize2. lia.
 * move=> r0 r1 d1 T0. eauto.
 * move=> A1 B0 C D d IH d0 IH1 T Hsize IH2 /=. rewrite /cplus_o.
   destruct T; rewrite /omap /obind /oapp.
   have: interp d (interp_wrap n) a. eauto. case Hcase: (interp _ _ _)=>//.
   rewrite /omap /obind /oapp.
   have: interp d0 (interp_wrap n) a. eauto. case Hcase: (interp _ _ _)=>//.
 * move=> a B0 C r T Hsize IH /=. rewrite /guard_o. destruct T.
   have: (interp_wrap n r a1). by eauto. case: (interp_wrap _ _ _)=>//.
Qed.

Lemma interp_wrap_sig : forall n r0 r1 (d : dsl_co r0 r1) (T : pTree r0), reg_size T < n -> { T' | interp_wrap n d T = Some T'}.
Proof.
move=> n r0 r1 d T Hsize.
move: (interp_wrap_some  n d T Hsize). case Hcase: (interp_wrap n d T)=>// [T'] _. econ. eauto.
Qed.

Lemma size_proof : forall (r : regex) (T : pTree r), leq ((reg_size T)) (reg_size T). done. Defined.

Definition interp_total (r0 r1 : regex) (d : dsl_co r0 r1) := 
fun T =>
match interp_wrap_sig (reg_size T).+1 d T (size_proof r0 T) with
| exist T' _ => T'
end.













(*let: (a,T') := T in if f T' is Some T'' then Some (a,T'') else None.*)

(*This judgment is redundant and we show why*)
(*Since dsl is intrinsically typed, there is a 1-to-1 correspondance between derivations in the rules from
 below and programs written in the dsl*)
Section Containment.
  Variable P : forall A B, dsl dsl_co A B -> Prop.
Reserved Notation "c0 <R= c1 ~> p" (at level 63).

Inductive ineq_gen : forall r0 r1, dsl dsl_co r0 r1 -> Prop :=
| rule_shuffle A B C : ineq_gen   (@shuffle _ A B C ) 
| rule_shuffleinv A B C : ineq_gen (@shuffleinv _ A B C)
| rule_retag A B : ineq_gen (@retag _ A B)
| rule_untagL A : ineq_gen (@untagL _ A)
| rule_untagLinv A :ineq_gen (@untagLinv _ A)
| rule_untag A :ineq_gen (@untag _ A)
| rule_tagL A B :ineq_gen (@tagL _ A B)
| rule_assoc A B C :ineq_gen (@assoc _ A B C)
| rule_associnv A B C :ineq_gen (@associnv _ A B C)
| rule_swap A :ineq_gen (@swap _ A)
| rule_swapinv A :ineq_gen (@swapinv _ A)
| rule_proj A :ineq_gen (@proj _ A)
| rule_projinv A :ineq_gen (@projinv _ A)
| rule_abortR A :ineq_gen (@abortR _ A)
| rule_abortRinv A :ineq_gen (@abortRinv _ A)
| rule_abortL A :ineq_gen (@abortL _ A)
| rule_abortLinv A :ineq_gen (@abortLinv _ A)
| rule_distL A B C :ineq_gen (@distL _ A B C)
| rule_distLinv A B C :ineq_gen (@distLinv _ A B C)
| rule_distR A B C :ineq_gen (@distR _ A B C)
| rule_distRinv A B C :ineq_gen (@distRinv _ A B C)
| rule_wrap A :ineq_gen (@wrap _ A)
| rule_wrapinv A :ineq_gen (@wrapinv _ A)
| rule_drop A :ineq_gen (@drop _ A)
| rule_dropinv A :ineq_gen (@dropinv _ A)
| rule_cid A :ineq_gen (@cid _ A)
| rule_ctrans A B C d0 d1 : ineq_gen d0 -> ineq_gen d1 -> ineq_gen (@ctrans _ A B C d0 d1)
| rule_cplus A A' B B' d0 d1 : ineq_gen d0 -> ineq_gen d1 -> ineq_gen (@cplus _ A A' B B' d0 d1)
| rule_cseq A A' B B' d0 d1 : ineq_gen d0 -> ineq_gen d1 -> ineq_gen (@cseq _ A A' B B' d0 d1)
| rule_cstar A B d : ineq_gen d ->  ineq_gen (@cstar _ A B d)
| rule_guard a A B d : P  d -> ineq_gen (@guard _ a A B (Co_build d)).
End Containment.
Hint Constructors ineq_gen.
Lemma c_ineq_gen_mon: monotone3 ineq_gen. 
Proof.
unfold monotone3.
intros. induction IN; eauto. 
Qed.
Hint Resolve c_ineq_gen_mon : paco.

Definition INEQ c0 c1 (d : dsl dsl_co c0 c1) := paco3 ineq_gen bot3 c0 c1 d.

Lemma dsl_to_derivation : forall c0 c1 (d: dsl dsl_co c0 c1), INEQ d.
Proof.
pcofix CIH.
move=> c0 c1. 
elim=>//;eauto.
- move=> A0 B C d HP d0 Hp0. pfold. con. pfold_reverse. pfold_reverse.
- move=> A0 A' B B' d Hp d0 Hp1. pfold. con. pfold_reverse. pfold_reverse.
- move=> A0 A' B B' d Hp d0 Hp1. pfold. con. pfold_reverse. pfold_reverse.
- move=> A0 B d Hp. pfold. con. pfold_reverse. 
- move=> a A0 B r0. pfold. destruct r0. econ. right. eauto.
Qed.

Lemma derivation_to_dsl : forall c0 c1 (d: dsl dsl_co c0 c1), @INEQ c0 c1 d ->  dsl dsl_co c0 c1.
Proof.
move=> c0 c1 d Hin. apply/d. 
Qed.


Lemma matchb_ref s r : reflect (Match s r) (matchb s r) .
Proof.
case Hcase: (matchb _ _). con. apply/matchbP=>//. con.
move/matchbP. rewrite Hcase//.
Qed.

Inductive Nu : regex -> Type := 
| N0 : Nu Eps 
| N1 c c' : Nu c -> Nu (c _+_ c')
| N2 c c' : Nu c' -> Nu (c _+_ c')
| N3 c c' : Nu c -> Nu c' -> Nu (c _;_ c')
| N4 c : Nu (Star c).
Hint Constructors Nu.

Lemma to_Nu : forall r, nu r -> Nu r.
Proof.
elim=>//=;eauto. 
move=> r IH r0 IH2. move=> Hor. destruct (nu r) eqn:Heqn. eauto. eauto.
move => r IH r0 IH2. move/andP. case. intros. eauto.
Qed. 

Definition nu_pTree (r : regex) (H : nu r) : (pTree r).
move: (to_Nu _ H). clear H.
elim=>//.
move => c c' Hnu T. apply/p_inl. done.
move=> c c' Hnu T. apply/p_inr. done.
move=> c. apply/fold_s. left. con.
Defined.

(*We use a unfolding rule that let's Coq produce an induction principle we can use*)
Inductive typing : forall r, pTree r -> Type := 
| T0 : typing Eps tt
| T1 (a : A)  : typing (Event a) (build_single _ a)
| T2 a : typing Empt a
| T3 r0 r1 T : typing r0 T -> typing (Plus r0 r1) (p_inl T)
| T4 r0 r1 T : typing r1 T -> typing (Plus r0 r1) (p_inr T)
| T5 r0 r1 T0 T1 : typing r0 T0 -> typing r1 T1 -> typing (Seq r0 r1) (T0, T1)
| T6 c T : typing Eps T -> typing (Star c) (fold_s (p_inl T))
| T7 c T : typing (c _;_ (Star c)) T -> typing (Star c) (fold_s (p_inr T)).

Hint Constructors typing.

Definition normalize (r : regex) : r <T= (o r) _+_ \big[Plus/Empt]_(i <- l) <

Lemma all_types : forall (r : regex) (T : pTree r), typing r T. 
Proof.
elim=>//;eauto. case=>//. 
move=> s. case. done. 
move=> r IH r0 IH2/=. case. move=> a. apply/T3. done. move=> b. apply/T4. done.
move=> r IH r0 IH2 /=. case. move=> a b. con. done. done.
move=> r IH /=. case. case. move=> a. con. case : a. done.
case. move=> a b. con. con. done. destruct b. 
destruct s. con. de u.
done.
con. done. done
move => x p. 
eapply (@eq_rect _ _ (fun y => typing (Event s) (existT (fun a' : A => a' == s) y _))).

apply T1.
econ.
rewrite /p.
Require Import Coq.Program.Equality.
dependent destruction p.
 Check eq_rect.  
apply/eq_rect.
apply/T1.
Search _ (_==_
move/eqP. econ.
rewrite (eqP p).
rewrite /pTree /=.   case0> inv T.
Fixpoint reg_size {r : regex} := 
fun T => let f := pTree in 
match r as r' return pTree r' -> nat with 
| Eps => fun _ => 0
| Empt => fun T => match T with end
| Event _ => fun _ => 1
| Plus r0 r1 => fun T => match T with 
                     | p_inl T' => @reg_size r0 T'
                     | p_inr T' => @reg_size r1 T'
                     end
| Seq r0 r1 => fun T => let: (T0,T1) := T in (@reg_size r0 T0) + (@reg_size r1 T1)
| Star r0 => fun T => match unfold_s T with 
                    | p_inl _ => 0 
                    | p_inr (T0,T1) => (@reg_size r0 T0) + (@reg_size (Star r0) T1)
                  end
end T.


Fixpoint flatten (n : nat) (r : regex) {struct n} : pTree r -> option (seq A) := 
if n is n'.+1 then
match r as r' return pTree r' -> option (seq A) with 
| Eps =>  fun _ => Some nil 
| Empt => fun T => match T with end 
| Event a => fun _ => Some (a::nil)
| Plus r0 r1 => fun T => match T with | p_inl T' => flatten n' r0 T' | p_inr T' => flatten n' r1 T' end
| Seq r0 r1 => fun T => let: (T0,T1) := T in obind (fun l => obind (fun l' => Some (l++l')) (flatten n' r1 T1)) (flatten n' r0 T0)
| Star r0 => fun T => match unfold_s T with 
                   | p_inl _ => Some nil
                   | p_inr (t,T') => obind (fun l => obind (fun l' => Some (l ++ l')) (flatten n' (Star r0) T')) (flatten n' r0 t)  
                  end 
end
else fun _ => None.

Fixpoint tree_size {r : regex} := 
fun T => let f := pTree in 
match r as r' return pTree r' -> nat with 
| Eps => fun _ => 0
| Empt => fun T => match T with end
| Event _ => fun _ => 1
| Plus r0 r1 => fun T => match T with 
                     | p_inl T' => @reg_size r0 T'
                     | p_inr T' => @reg_size r1 T'
                     end
| Seq r0 r1 => fun T => let: (T0,T1) := T in (@reg_size r0 T0) + (@reg_size r1 T1)
| Star r0 => fun L => foldr (fun x acc => (@reg_size r0 x) + acc) 0  L 
end T.


Definition tree_of_match (s : trace) (r : regex) (H : matchb s r) : (pTree r).
rewrite /matchb in H.
elim : s r H.
-  case=>//=.
 * move=> r r0 /=. rewrite /matchb.
move=> _. con.
 * move=>//.
 * move=>//
 
move=>r _.

Fixpoint as_prop (r : regex) : Prop := 
match r with 
| Eps => True
| Empt => False
| Event a => exists x, x = a 
| Plus r0 r1 => (as_prop r0) \/ (as_prop r1)
| Seq r0 r1 => (as_prop r0) /\ (as_prop r1)
| Star r0 => Forall (fun x => as_prop r0)
end. 

Fixpoint tree_of_match (s : trace) (r : regex) (H : Match s r) : option (pTree r) := 
match H in Match s r return option (pTree r) with 
| MEps => Some tt
| _ => None
end.




(*Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.*)

(*Inductive dsl3 :  Set := 
| shuffle3  : regex-> dsl3. ((A _+_ B) _+_ C) (A _+_ (B _+_ C)).
| ctrans3 (A B C: regex) : dsl3 R A B -> dsl3 R B C -> dsl3 R A C
| cplus3 (A B C D: regex) : dsl3 R A B -> dsl3 R C D -> dsl3 R (A _+_ C) (B _+ D)
| guard3 (A B : regex) : R A B -> dsl3 R A B.*)












































Definition dsl_2_fix := cfix (ctrans shuffle (cfix (cplus (guard (var_dsl 1)) (guard (var_dsl 0))))).

Definition shuffle_inv A B C := cofix f0 := Co_build (ctrans2 (@shuffle2 _ A B C) shuffleinv2). 

Inductive c2_ineq : forall r0 r1, dsl2 dsl_co r0 r1 -> Prop :=
| rule2_shuffle c0 c1 c2 : c2_ineq (*((c0 _+_ c1) _+_ c2) (c0 _+_ (c1 _+_ c2))*) (@shuffle2 dsl_co c0 c1 c2). (*assoc  + *)



Definition dsl_co_1_fix A B C := cofix f0 := Co_build (ctrans2 (@shuffle2 A B C) (cplus2 (guard2 f0) (guard2 f0))).

Definition co_helper f0 := cofix f1 := Co_build (cplus2 (guard2 f0) (guard2 f1)).

Definition dsl_co_2_fix := cofix f0 := Co_build (ctrans2 shuffle2 (cplus2 (guard2 f0) (guard2 (co_helper f0)))).

Definition co_trans_left_right := cofix f := Co_build (ctrans2 shuffle2 
                                                      (ctrans2 (cplus2 shuffle2 (guard2 f))
                                                               (cplus2 (guard2 f) shuffle2))).



(*

shuffle : forall A B C, (A + B) + C -> A + (B + C)
shuffleinv : forall A B C, A + (B + C) -> (A + B) + C
trans : forall A B C, (A -> B) -> (B -> C) -> A -> C

shuffle ; shuffleinv : forall A B C,  (A + B) + C ->  (A + B) + C


*)

Fixpoint from (d : dsl2) := 
match d with 
| shuffle2 => forall c0 c1 c2, (c0 _+_ c1) _+_ c2
| ctrans2 d0 _ => ctrans2 d0
| cplus2 d0 d1 => (from d0) _+_ (from d1)





Check shuffle_i.
Fixpoint interp (d : dsl2) : (pTree (from d)) -> (pTree (to d)) :=
fun T => 
match d with 
| shuffle2 => shuffle_i
| ctrans2 p0 p1 => (interp p0) \o (interp p1)
| cplus p0 p1 => cplus_i
| guard2 p_co => 

Definition dsl2_type (d : dsl) : Type := 
match d with 
| shuffle => forall c0 c1 c2, ((c0 _+_ c1) _+_ c2) <T= (c0 _+_ (c1 _+_ c2))
| shuffleinv => forall c0 c1 c2, c0 _+_ (c1 _+_ c2)  <T= (c0 _+_ c1) _+_ c2 
| retag => forall c0 c1, c0 _+_ c1 <T= c1 _+_ c0
| untagL => forall c, Empt _+_ c <T= c
| untagLinv => forall c, c <T= Empt _+_ c
| untag => forall c, c _+_ c <T= c
| _ => unit
end.




(*Notation " ( c ) *" := (Star c).*)

(*Definition unf_ineq : (regex -> regex -> dsl -> Prop) -> regex -> regex -> dsl -> Prop := 
  (Unf ) \o c_ineq.

Inductive ineq (R : regex -> regex -> dsl -> Prop) : regex -> regex -> dsl -> Prop :=
| ind_rules r0 r1 d : unf_ineq (ineq R) r0 r1 d -> ineq R r0 r1 d
| co_rule r0 r1 d a : R r0 r1 d -> ineq R ((Event a) _;_ r0) ((Event a) _;_ r1) d.
*)

(*Definition interpret_dsl  (p : dsl) s r r' (H: Match s r) : Match s r'.
case: H.
- 
match p with 
| *)

Check ApplyF1.
Inductive invPred_gen (R : dsl -> Prop) : dsl -> Prop := 
  | ip_shuffle pf : full_unf pf = shuffle -> invPred_gen R pf
  | ip_shuffleinv pf : full_unf pf =shuffleinv  ->  invPred_gen R pf
  | ip_retag pf : full_unf pf =retag  ->  invPred_gen R pf
  | ip_untagL pf : full_unf pf = untagL ->  invPred_gen R pf
  | ip_untagLinv pf : full_unf pf = untagLinv ->  invPred_gen R pf
  | ip_untag pf : full_unf pf = untag ->  invPred_gen R pf
  | ip_tagL pf : full_unf pf =tagL ->  invPred_gen R pf
  | ip_assoc pf : full_unf pf =assoc  ->  invPred_gen R pf
  | ip_associnv pf : full_unf pf =associnv  ->  invPred_gen R pf
  | ip_swap pf : full_unf pf =swap ->  invPred_gen R pf
  | ip_swapinv pf : full_unf pf = swapinv ->  invPred_gen R pf
  | ip_proj pf : full_unf pf = proj ->  invPred_gen R pf
  | ip_projinv pf : full_unf pf =projinv   ->  invPred_gen R pf
  | ip_abortR pf : full_unf pf = abortR  ->  invPred_gen R pf
  | ip_abortRinv pf : full_unf pf = abortRinv  ->  invPred_gen R pf
  | ip_abortL pf : full_unf pf =  abortL ->  invPred_gen R pf
  | ip_abortLinv pf : full_unf pf = abortLinv  ->  invPred_gen R pf
  | ip_distL pf : full_unf pf = distL  ->  invPred_gen R pf
  | ip_distLinv pf : full_unf pf = distLinv  ->  invPred_gen R pf
  | ip_distR pf : full_unf pf =  distR ->  invPred_gen R pf
  | ip_distRinv pf : full_unf pf =distRinv   ->  invPred_gen R pf
  | ip_wrap pf : full_unf pf =  wrap ->  invPred_gen R pf
  | ip_wrapinv pf : full_unf pf = wrapinv  ->  invPred_gen R pf
  | ip_drop pf : full_unf pf = drop  ->  invPred_gen R pf
  | ip_dropinv pf : full_unf pf = dropinv  ->  invPred_gen R pf
  | ip_cid pf : full_unf pf = cid  ->  invPred_gen R pf
  | ip_ctrans p0 p1 pf  : full_unf pf = ctrans p0 p1 -> invPred_gen R p0 -> invPred_gen R p1  -> invPred_gen R pf
  | ip_cplus p0 p1 pf : full_unf pf =  (cplus p0 p1) ->  invPred_gen R p0 -> invPred_gen R p1  -> invPred_gen R pf
  | ip_cseq p0 p1 pf : full_unf pf = (cseq p0 p1)  ->  invPred_gen R p0 -> invPred_gen R p1 -> invPred_gen R pf
  | ip_cstar p pf : full_unf pf = (cstar p)  ->  invPred_gen R p -> invPred_gen R pf
(*  | cfix : dsl -> dsl*)
  | guard p pf : full_unf pf = guard p -> R p -> invPred_gen R pf.
Hint Constructors invPred_gen.

Lemma invPred_gen_mon : monotone1 invPred_gen.
Proof.
move=> x r r'. elim=>//;eauto.
Qed.
Hint Resolve invPred_gen_mon : paco.

Definition invPred g := paco1 ( ApplyF1 full_unf \o invPred_gen) bot1 g.

Lemma invPred_unf : forall R p, invPred_gen R (full_unf p) -> invPred_gen R p.
Proof.
move=> R p. move Heq: (full_unf _)=>ef Hinv.
elim: Hinv Heq.
- move=> pf Heq0 Heq1. subst. 

Lemma to_invPred : forall r0 r1 p, r0 <C= r1 ~> p -> invPred p.
Proof.
pcofix CIH. move => r0 r1 p. sunfold. elim=>//.
all: try solve[intros; subst; pfold; con; rewrite H //;eauto].
move=> c0 c1 c2 pf p0 p1 Hunf HC Hp Hc' HP2. pfold. con. rewrite Hunf. apply/ip_ctrans.  con. 
punfold Hp. inv Hp.

con=>//. punfold Hp. inv Hp.

27 : { intros. subst.
move=>_ _ _ pf.



(*Variant Unf (R :  dsl -> Prop) : dsl  -> Prop :=
 Unf1_intro a b c :  R a b (full_unf c) -> Unf R a b c.*)

Lemma Unf_mon  : monotone3 Unf. 
Proof. intro. intros. inv IN. con. eauto. Qed. 


Hint Resolve Unf_mon : paco.


Derive Inversion_clear Unf_inv with (forall  (R : (regex -> regex -> dsl -> Prop) -> regex -> regex -> dsl -> Prop) (P : regex -> regex -> dsl -> Prop) a b c, 
                                          (Unf \o R) P a b c) Sort Prop.









Notation "p0 ;c; p1" :=(ctrans p0 p1)(at level 63).

Check eq_rect.

(*Ineffecient program*)
Definition d6 := (ctrans (cstar wrapinv)
              (ctrans drop
                 (ctrans wrapinv
                    (ctrans
                       (cplus cid
                          (ctrans assoc
                             (cseq cid
                                (cfix
                                   (ctrans (cseq cid dropinv)
                                      (ctrans (cseq cid (cstar wrap))
                                         (cfix
                                            (ctrans (cseq wrapinv cid)
                                               (ctrans distR (ctrans (cplus proj cid) (ctrans (ctrans ((ctrans
             (ctrans
                (ctrans
                   (ctrans
                      (ctrans
                         (cplus
                            (ctrans (cstar wrapinv)
                               (ctrans drop (ctrans wrapinv (ctrans (cplus cid (ctrans assoc (guard ((var_dsl 1))))) wrap))))
                            (ctrans assoc (guard ((var_dsl 0))))) tagL) retag) (cplus cid (cplus projinv cid)))
                (cplus cid distRinv)) (cplus cid (cseq cid dropinv)))) wrap) drop)))))))))))
                       wrap)))).


Lemma test : forall a,  (Star (Star (Event a))) <C= (Star (Event a)) ~> d6.
Proof.
move=> a.  pfold.

apply: rule_ctrans=>//. apply: rule_cstar=>//. apply: rule_wrapinv=>//.

apply/rule_ctrans=>//. apply/rule_drop=>//.
apply/rule_ctrans=>//. apply/rule_wrapinv=>//.
apply/rule_ctrans=>//. 2: { apply/rule_wrap=>//. }
apply/rule_cplus=>//. apply/rule_cid=>//.
apply/rule_ctrans=>//. apply/rule_assoc=>//.
(*apply/rule_test=>//. left. pcofix CIH. pfold*)  
apply/rule_cseq=>//. apply/rule_cid=>//. (*Don't use rule_test yet*) (*apply/rule_test=>//. left=>//. pfold.*)

pfold_reverse. pcofix CIH. pfold. (*pcofix before cfix*)
(*apply/rule_cfix=>//. simpl=>//. *)

apply: rule_ctrans. rewrite /full_unf //=. 
apply/rule_cseq=>//. apply/rule_cid=>//. apply/rule_dropinv=>//.

apply/rule_ctrans=>//. apply/rule_cseq=>//. apply/rule_cid=>//. apply/rule_cstar/rule_wrap=>//. 


pfold_reverse=>//. pcofix CIH2=>//. pfold=>//. (*pcofix before cfix*)
(*apply/rule_cfix=>//. simpl=>//. *)



apply/rule_ctrans. rewrite /full_unf //=. apply/rule_cseq=>//. apply/rule_wrapinv=>//. apply/rule_cid=>//.
apply/rule_ctrans=>//. apply/rule_distR=>//.
apply/rule_ctrans=>//. apply/rule_cplus=>//. apply/rule_proj=>//. apply/rule_cid=>//.
apply/rule_ctrans=>//. 2: { apply/rule_drop=>//. }
apply/rule_ctrans=>//. 2: { apply/rule_wrap=>//. }

(*Unset Printing Notations.*)
apply/rule_ctrans=>//. 2: { apply/rule_cplus=>//. apply/rule_cid=>//. apply/rule_cseq=>//. apply/rule_cid=>//. apply/rule_dropinv=>//. }
apply/rule_ctrans=>//. 2: { apply/rule_cplus=>//. apply/rule_cid=>//. apply/rule_distRinv=>//. }




apply/rule_ctrans=>//. 2: { apply/rule_cplus=>//. apply/rule_cid=>//. apply/rule_cplus=>//. apply/rule_projinv=>//. apply/rule_cid=>//. }
apply/rule_ctrans=>//. 2: { apply/rule_retag=>//. }
apply/rule_ctrans=>//. 2: { apply/rule_tagL=>//. }


apply/rule_cplus=>//. 

apply/rule_ctrans=>//. apply/rule_cstar/rule_wrapinv=>//. 
apply/rule_ctrans=>//. apply/rule_drop=>//.
apply/rule_ctrans=>//. apply/rule_wrapinv=>//.
apply/rule_ctrans=>//. 2: { apply/rule_wrap=>//. }
apply/rule_cplus=>//. apply/rule_cid=>//.
apply/rule_ctrans=>//. apply/rule_assoc=>//.
apply/rule_test=>//. right. apply/CIH.

apply/rule_ctrans=>//. apply/rule_assoc=>//.
apply/rule_test=>//. right.  apply/CIH2.
Qed.




(*Definition dsl_in (d: dsl) : Type := 
match full_unf d with 
| shuffle => regex * regex * regex
| shuffleinv => regex * regex * regex
| retag => regex * regex
| _ =>  unit
end. *)

(*Definition shuffle_Type (A B C : Type) : ((A + B) + C) -> (A + (B + C)) :=
fun  T => 
match T with 
| p_inl (p_inl T') => p_inl T'
| p_inl (p_inr T') => p_inr (p_inl T')
| p_inr T' => p_inr (inr T')
end.*)



Definition dsl_type (d : dsl) : Type := 
match d with 
| shuffle => forall c0 c1 c2, ((c0 _+_ c1) _+_ c2) <T= (c0 _+_ (c1 _+_ c2))
| shuffleinv => forall c0 c1 c2, c0 _+_ (c1 _+_ c2)  <T= (c0 _+_ c1) _+_ c2 
| retag => forall c0 c1, c0 _+_ c1 <T= c1 _+_ c0
| untagL => forall c, Empt _+_ c <T= c
| untagLinv => forall c, c <T= Empt _+_ c
| untag => forall c, c _+_ c <T= c
| _ => unit
end.









Fixpoint interp (d : dsl) :  dsl_type (full_unf d)  :=
match full_unf d  as d' return (dsl_type d') with 
| shuffle => shuffle_i
| shuffleinv => shuffleinv_i
| retag => retag_i
| untagL => untagL_i
| untagLinv => untagLinv_i
| untag => untag_i
| _ => tt
end.

Check interp.





(*Definition d := (cstar wrapinv;c;
            (drop;c;
             (wrapinv;c;
              (cplus cid
                 (assoc;c;
                  cseq cid
                    (guard
                       (cseq cid dropinv;c;
                        (cseq cid (cstar wrap);c;
                         (cseq wrapinv cid;c;
                          (distR;c;
                           (cplus proj cid;c;
                            (((((((cplus cid (**) cid(**);c; tagL);c; retag);c; cplus cid (cplus projinv cid));c;
                                cplus cid distRinv);c; cplus cid (cseq cid dropinv));c; wrap);c; drop))))))));c; wrap)))).*)


(*Definition d' := (cseq cid dropinv;c;
           (cseq cid (cstar wrap);c;
            cfix
              (cseq wrapinv cid;c;
               (distR;c;
                (cplus proj cid;c;
                 (((((((cplus
                          (cstar wrapinv;c; (drop;c; (wrapinv;c; (cplus cid (assoc;c; cseq cid (guard (var_dsl 0)));c; wrap))))
                          (assoc;c; cseq cid (guard (var_dsl 0)));c; tagL);c; retag);c; cplus cid (cplus projinv cid));c;
                     cplus cid distRinv);c; cplus cid (cseq cid dropinv));c; wrap);c; drop)))))).*)

Definition d' := (cstar wrapinv;c;
            (drop;c;
             (wrapinv;c;
              (cplus cid
                 (assoc;c;
                  cseq cid
                    (cfix
                       (cseq cid dropinv;c;
                        (cseq cid (cstar wrap);c;
                         cfix
                           (cseq wrapinv cid;c;
                            (distR;c;
                             (cplus proj cid;c;
                              (((((((cplus (cstar wrapinv;c; (drop;c; (wrapinv;c; (cplus cid (assoc;c; cseq cid (guard (var_dsl 1)));c; wrap)))) 
                                           (assoc;c; cseq cid (guard (var_dsl 0))));c; tagL);c; retag);c; cplus cid (cplus projinv cid));c;
                                  cplus cid distRinv);c; cplus cid (cseq cid dropinv));c; wrap);c; drop))))))));c; wrap))).



Definition d3 := (ctrans
             (ctrans
                (ctrans
                   (ctrans
                      (ctrans
                         (cplus
                            (ctrans (cstar wrapinv)
                               (ctrans drop (ctrans wrapinv (ctrans (cplus cid (ctrans assoc (cseq cid (guard (var_dsl 1))))) wrap))))
                            (ctrans assoc (cseq cid (guard (var_dsl 0))))) tagL) retag) (cplus cid (cplus projinv cid)))
                (cplus cid distRinv)) (cplus cid (cseq cid dropinv))) .


Definition d4 := (ctrans (cstar wrapinv)
              (ctrans drop
                 (ctrans wrapinv
                    (ctrans
                       (cplus cid
                          (ctrans assoc
                             (cseq cid
                                (cfix
                                   (ctrans (cseq cid dropinv)
                                      (ctrans (cseq cid (cstar wrap))
                                         (cfix
                                            (ctrans (cseq wrapinv cid)
                                               (ctrans distR (ctrans (cplus proj cid) (ctrans (ctrans d3 wrap) drop)))))))))))
                       wrap)))).


Definition d5 := (ctrans (cstar wrapinv)
              (ctrans drop
                 (ctrans wrapinv
                    (ctrans
                       (cplus cid
                          (ctrans assoc
                             (cseq cid
                                (cfix
                                   (ctrans (cseq cid dropinv)
                                      (ctrans (cseq cid (cstar wrap))
                                         (cfix
                                            (ctrans (cseq wrapinv cid)
                                               (ctrans distR (ctrans (cplus proj cid) (ctrans (ctrans ((ctrans
             (ctrans
                (ctrans
                   (ctrans
                      (ctrans
                         (cplus
                            (ctrans (cstar wrapinv)
                               (ctrans drop (ctrans wrapinv (ctrans (cplus cid (ctrans assoc (cseq cid (guard (var_dsl 1))))) wrap))))
                            (ctrans assoc (cseq cid (guard (var_dsl 0))))) tagL) retag) (cplus cid (cplus projinv cid)))
                (cplus cid distRinv)) (cplus cid (cseq cid dropinv)))) wrap) drop)))))))))))
                       wrap)))).








(*Lemma test2 : forall a , exists p,  paco3 c_ineq bot3 (Plus (Star (Star (Event a))) (Seq (Seq (Event a) (Star (Event a))) (Star (Star (Event a)))))
    (Plus Eps (Seq (Plus Eps (Event a)) (Star (Plus Eps (Event a))))) p.
Proof.
move=> a. econ. pcofix CIH. pfold.
apply/rule_ctrans. 2: { apply/rule_cplus. apply/rule_cid. apply/rule_cseq. apply/rule_cid. apply/rule_dropinv. }
apply/rule_ctrans. 2: { apply/rule_cplus. apply/rule_cid. apply/rule_distRinv. }




apply/rule_ctrans. 2: { apply/rule_cplus. apply/rule_cid. apply/rule_cplus. apply/rule_projinv. apply/rule_cid. }
apply/rule_ctrans. 2: { apply/rule_retag. }
apply/rule_ctrans. 2: { apply/rule_tagL. }


apply/rule_cplus. 

apply/rule_ctrans. apply/rule_cstar/rule_wrapinv. 
apply/rule_ctrans. apply/rule_drop.
apply/rule_ctrans. apply/rule_wrapinv.
apply/rule_ctrans. 2: { apply/rule_wrap. }
apply/rule_cplus. apply/rule_cid.
apply/rule_ctrans. apply/rule_assoc.
apply/rule_test. right. instantiate (1:= var_dsl 1). admit. 

apply/rule_ctrans. apply/rule_assoc.
apply/rule_test. right. instantiate (1:= var_dsl 0).
Unset Printing Notations.
 admit.
pfold.
*)

Lemma monotone_comp3 : forall (A B C : Type) (F0 F1 : (A -> B -> C -> Prop) -> (A -> B -> C -> Prop)),  
monotone3 F0 -> monotone3 F1 -> monotone3 (F0 \o F1). 
Proof. intros. move => x0 x1 x2. intros. apply/H. eauto. eauto. 
Qed.
Hint Resolve monotone_comp3 : paco.

(*Lemma fold_back : forall R c0 c1 p' p, p' = full_unf p -> unf_ineq R c0 c1 p -> c_ineq R c0 c1 p'.
Proof.
move=> R c0 c1 p dsl Heq HC. subst. inv HC.
Qed.

Lemma fold_back2 : forall R c0 c1 p, mu_height p = 0 -> unf_ineq R c0 c1 p -> c_ineq R c0 c1 p.
Proof.
move => r c0 c1 p Hheight HC. have : p = full_unf p. rewrite /full_unf Hheight //=. 
move=>->. apply/fold_back. done. done.
Qed.

Ltac acc H := con;con;apply: H.*)

(*Rules use unfolding to avoid explicit fix rule which would require productivity requirements for soundness
  always working on unfolded terms prevents this without any conditions on the dsl*)



Definition contains c c' := forall s, Match s c -> Match s c'.

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

Lemma test : forall a, Contains (Star (Star a)) (Star a).
Proof.
move => a. pfold. con=>//=.
move=> e. left. pfold. con=>//.
move=> e0. left. rewrite /= andbC /=. case_if.
simpl. admit. 
 rewrite /derive.
Set Printing All. rewrite /=. rewrite /derive.
simpl.




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
Print regex. Print sig. Print sigT. Locate sigT.
Print unit.
Locate unit.




Lemma add_comm : forall n n', n + n' = n' + n.
Proof.
elim. 
- move=> n'. rewrite /=. rewrite /addnE.
induction n.
-  intros. Set Printing All.

Locate "+".
Print addn. Print addn_rec. Print Nat.add.




Fixpoint dsl_type (d : dsl) := 
match d with 
| shuffle =>  
fun r => match r in regex*regex*regex return _ => with (r0,r1,r2) => pTree ((r0 _+_ r1) _+_ r2) ->  pTree (r0 _+_ (r1 _+_ r2)) end
| shuffleinv => fun r => let: (r0,r1,r2) := r in  pTree (r0 _+_ (r1 _+_ r2))  -> pTree ((r0 _+_ r1) _+_ r2) 
| retag => fun r => let: (r0,r1):= r in  pTree (r0 _+_ r1)  -> pTree (r1 _+_ r0)
| _ =>  fun _ =>  A
end. 

Fixpoint dsl_type (d : dsl) : (dsl_in d)  -> Type := 
match d with 
| shuffle => fun r => match r in regex*regex*regex return _ => with (r0,r1,r2) => pTree ((r0 _+_ r1) _+_ r2) ->  pTree (r0 _+_ (r1 _+_ r2)) end
| shuffleinv => fun r => let: (r0,r1,r2) := r in  pTree (r0 _+_ (r1 _+_ r2))  -> pTree ((r0 _+_ r1) _+_ r2) 
| retag => fun r => let: (r0,r1):= r in  pTree (r0 _+_ r1)  -> pTree (r1 _+_ r0)
| _ =>  fun _ =>  A
end. 



Check shuffle_i. Check (dsl_type shuffle).
Eval simpl in (dsl_in shuffle).

Definition shuffleinv_i r0 r1 r2  : (dsl_type shuffleinv r0 r1 r2) :=

Definition retag_i r0 r1 r2 : (dsl_type retag r0 r1 r2) :=


Definition interp (d : dsl) := 
match full_unf d with 
| shuffle => Some (shuffle_i )
| shuffleinv => Some (shuffleinv_i )
| retag => Some (retag_i )
| cfix d' => fix 
end.

Definition dsl_in' (d: dsl) (T : Type) : Type := 
match d with 
| shuffle => regex -> regex -> regex -> T
| shuffleinv => regex -> regex -> regex -> T
| retag => regex -> regex -> T
| _ =>  unit -> T
end. 

Fixpoint dsl_type' (d : dsl) : (dsl_in' d Type) := 
match d with 
| shuffle => fun r0 r1 r2 =>  pTree ((r0 _+_ r1) _+_ r2) ->  pTree (r0 _+_ (r1 _+_ r2))
| shuffleinv => fun r0 r1 r2 =>  pTree (r0 _+_ (r1 _+_ r2))  -> pTree ((r0 _+_ r1) _+_ r2) 
| retag => fun r0 r1 => pTree (r0 _+_ r1)  -> pTree (r1 _+_ r0)
| _ =>  fun _ =>  A
end. 





Print plus. Print Nat.add.

Check interp.

Definition my_fix (l0 l1 : seq (A * regex))  (f : pTree r0 -> pTree r1) : 
  (pTree (\big[Plus/Empt]_(i <- l0) ((Event i.1) _;_ i.2))) ->
  (pTree (\big[Plus/Empt]_(i <- l1) ((Event i.1) _;_ i.2))) := 
 pTree ()
-> pTree r1  := 
fun T => 

Check dsl_type.
| rule_retag c0 c1: c0 _+_ c1 <R= c1 _+_ c0 ~> retag (*comm +*)(*Other direction is redundant*)




Definition interpret (d : dsl) := 
match d with 
| shuffle => shuffle_i
| _ => shuffle_i
end.

Inductive term : Type :=
| t_tt : term
| t_singl : A -> term
| t_inl : term -> term
| t_inr : term -> term
| t_pair : term -> term -> term
| t_fold : term -> term.


(*Alternative Matching definition similar to isorecursive type inhabitation*)
(*Also try interpreting coercion directly to Match derivation maybe? What is the difference*)
Inductive Types (r : regex) : (from_regex r) -> regex -> Prop :=
  | T0 : Types r tt  Eps.
  | T1 x : Types (t_singl x) (Event x)
  | T2 t0 c1 t1 c2 :
             Types t0 c1 ->
             Types t1 c2 ->
             Types (t_pair t0 t1) (c1 _;_ c2)
  | T3 s1 c1 c2:
               Types s1 c1 ->
               Types (t_inl s1) (c1 _+_ c2)
  | T4 c1 s2 c2:
               Types s2 c2 ->
               Types (t_inr s2) (c1 _+_ c2)
  | T5 c s :
                Types s (Eps _+_ (c _;_ (Star c))) ->
                Types (t_fold s) (Star c).
Hint Constructors Types.

Fixpoint t_flatten (t : term) := 
match t with 
| t_tt => nil
| t_singl a => a :: nil
| t_pair t0 t1 => (t_flatten t0)++(t_flatten t1)
| t_inl t' => t_flatten t' 
| t_inr t' => t_flatten t' 
| t_fold t' => t_flatten t'
end.




Definition shuffle_i (t : term)
Print dsl.
Fixpoint interpret (d : dsl) :=
match d with 
| shuffle => 


Lemma TypesP: forall s c, Match s c <-> Types s c.
Proof.
move => s c. split;first by elim;eauto.
elim;eauto.
move=> c0 s0 HM HM2. inv HM2.
inv H1. inv H1. con. done. done.
Qed.


Lemma c_eq_gen_mon: monotone2 c_eq. 
Proof.
unfold monotone2.
intros. induction IN; eauto. 
apply/c_fix. done. elim: H0 LE;eauto.
Qed.
Hint Resolve c_eq_gen_mon : paco.

End Regex.
