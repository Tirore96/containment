From HB Require Import structures.


From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
From Containment Require Import  utils dsl dsl_theory.




Let inE := utils.inE.

Section Regex.
Variable (A : finType).
Definition trace := seq A.

Inductive regex : Type :=
| Eps : regex
| Empt : regex
| Event : A -> regex
| Plus : regex -> regex -> regex
| Seq : regex -> regex -> regex
| Star : regex -> regex.

(*Notation "e _._ c" := (Seq (Event e) c)
                    (at level 51, right associativity).*)

Notation "c0 _;_ c1"  := (Seq c0 c1)
                         (at level 52, left associativity).

Notation "c0 _+_ c1"  := (Plus c0 c1)
                         (at level 53, left associativity).

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
| c_fix (l0 l1 : seq (A * regex)) : Forall2 (fun x y => x.1 = y.1) l0 l1 -> Forall2 (fun r0 r1 => co_eq r0.2 r1.2) l0 l1 ->
                                    \big[Plus/Empt]_(i <- l0) ((Event i.1) _;_ i.2) =R=  
                                    \big[Plus/Empt]_(i <- l1) ((Event i.1) _;_ i.2)

 where "c1 =R= c2" := (c_eq c1 c2).
End Equivalence.
Hint Constructors c_eq.

Section Equivalence_Properties.

Lemma c_eq_gen_mon: monotone2 c_eq. 
Proof.
unfold monotone2.
intros. induction IN; eauto. 
apply/c_fix. done. elim: H0 LE;eauto.
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
clear H.
elim: H0=>//. move=> x y l l' R' Hfor IH.
rewrite !big_cons //=.
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


Lemma c_fix_derive : forall l0 l1 R e,
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
Qed.

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
- apply c_fix_derive. done. clear H. elim: H0. done. move=> x y l l' [] // HC Hfor Hfor'. con. punfold HC. 
  done.
Qed.


Set Implicit Arguments.
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
apply/c_fix.
elim: (index_enum A). done. 
move=> a l IH /=. con. done. done. 
elim: (index_enum A)=>/=. done. 
move=> a l IH. con. right. apply/CIH=>/=. move: (H1 a). case=>//. done.
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




Section Containment.
  Variable co_ineq : regex -> regex -> dsl -> Prop.
Reserved Notation "c0 <R= c1 ~> p" (at level 63).


(*Maybe c_star_ctx and c_star_plus are not necessary*)

(*Tried as much as possible to stay within Henglein & Nielsen's formulation*)
Inductive c_ineq : regex -> regex -> dsl -> Prop :=
| rule_shuffle c0 c1 c2 : (c0 _+_ c1) _+_ c2 <R= c0 _+_ (c1 _+_ c2) ~> shuffle (*assoc  + *)


| rule_shuffleinv c0 c1 c2 : c0 _+_ (c1 _+_ c2)  <R= (c0 _+_ c1) _+_ c2 ~> shuffleinv (*assoc +*)

| rule_retag c0 c1: c0 _+_ c1 <R= c1 _+_ c0 ~> retag (*comm +*)(*Other direction is redundant*)

| rule_untagL c: Empt _+_ c <R= c ~> untagL (* + neut r*)
| rule_untagLinv c: c <R= Empt _+_ c ~> untagLinv (*Possibly redundant*)

| rule_untag c : c _+_ c <R= c ~> untag (*idem*)
| rule_tagL c d : c <R= c _+_ d ~> tagL

| rule_assoc c0 c1 c2 : (c0 _;_ c1) _;_ c2 <R= c0 _;_ (c1 _;_ c2) ~> assoc
| rule_associnv c0 c1 c2 : c0 _;_ (c1 _;_ c2) <R=  (c0 _;_ c1) _;_ c2 ~> associnv

| rule_swap c : (c _;_ Eps) <R= (Eps _;_ c) ~> swap (*New rule, from regex as types paper*)
| rule_swapinv c :  (Eps _;_ c) <R= (c _;_ Eps) ~> swapinv

| rule_proj c : (Eps _;_ c) <R= c ~> proj 
| rule_projinv c : c <R=(Eps _;_ c) ~> projinv

| rule_abortR c :  c _;_ Empt <R= Empt ~> abortR
| rule_abortRinv c :  Empt  <R= c _;_ Empt ~> abortRinv

| rule_abortL c : Empt _;_ c <R=  Empt ~> abortL
| rule_abortLinv c : Empt  <R=  Empt _;_ c ~> abortLinv

| rule_distL c0 c1 c2 : c0 _;_ (c1 _+_ c2) <R= (c0 _;_ c1) _+_ (c0 _;_ c2) ~> distL
| rule_distLinv c0 c1 c2 : (c0 _;_ c1) _+_ (c0 _;_ c2)  <R=  c0 _;_ (c1 _+_ c2) ~> distLinv

| rule_distR c0 c1 c2 : (c0 _+_ c1) _;_ c2 <R= (c0 _;_ c2) _+_ (c1 _;_ c2) ~> distR
| rule_distRinv c0 c1 c2 :  (c0 _;_ c2) _+_ (c1 _;_ c2)  <R= (c0 _+_ c1) _;_ c2 ~> distRinv


| rule_wrap c :  Eps _+_ (c _;_ Star c) <R= Star c ~> wrap 
| rule_wrapinv c :  Star c  <R=Eps _+_ (c _;_ Star c) ~> wrapinv

| rule_drop c :  Star (Eps _+_ c) <R= Star c ~> drop
| rule_dropinv c :  Star c <R= Star (Eps _+_ c) ~> dropinv (*Possibly redundant*)

 (*We want to remove inner Eps, so we only keep this one for now*)
(*Will the other direction be necessary?*)
(*| ci_star_plus_inv c :  Star c  <R= Star (Eps _+_ c) (*Could possibly be removed but we are studying the computational interpretation of EQ rules*) *)

| rule_cid c : c <R= c ~> cid
(*| ci_sym c0 c1 (H: c0 =R=c1) : c1 =R=c0*)
| rule_ctrans c0 c1 c2 p0 p1 (H1 : c0 <R=c1 ~> p0 ) (H2 : c1 <R=c2 ~> p1) : c0 <R=c2 ~> ctrans p0 p1
| rule_cplus c0 c0' c1 c1' p0 p1 (H1 : c0 <R=c0' ~> p0) (H2 : c1 <R=c1' ~> p1) : c0 _+_ c1 <R=c0' _+_ c1' ~> cplus p0 p1
| rule_cseq c0 c0' c1 c1' p0 p1 (H1 : c0 <R=c0' ~> p0) (H2 : c1 <R=c1' ~> p1) : c0 _;_ c1 <R=c0' _;_ c1' ~> cseq p0 p1
| rule_cstar c0 c1 p (H : c0 <R=c1 ~> p) : Star c0 <R= Star c1 ~> cstar p  (*new context rule*) 
| rule_cfix r r' (p  : dsl) : r <R= r' ~> p[d (cfix p) .: var_dsl] ->  r <R= r' ~> (cfix p)
| rule_test a r r' p : co_ineq r r' p -> (Event a) _;_ r <R= (Event a) _;_ r' ~> (cseq cid (guard p))

 where "c1 <R= c2 ~> p" := (c_ineq c1 c2 p).
End Containment.
Hint Constructors c_ineq.
Lemma c_ineq_gen_mon: monotone3 c_ineq. 
Proof.
unfold monotone3.
intros. induction IN; eauto. 
Qed.
Hint Resolve c_ineq_gen_mon : paco.


(*Definition interpret_dsl  (p : dsl) s r r' (H: Match s r) : Match s r'.
case: H.
- 
match p with 
| *)

Notation "c0 < ( R ) = c1 ~> p" := (c_ineq R c0 c1 p)(at level 63).
Definition INEQ c0 c1 p := paco3 c_ineq bot3 c0 c1 p.
Notation "c0 <C= c1 ~> p" := (INEQ c0 c1 p)(at level 63).
Notation " ( c ) *" := (Star c).

Notation "p0 ;c; p1" :=(ctrans p0 p1)(at level 63).


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
Lemma test : forall a,  (Star (Star (Event a))) <C= (Star (Event a)) ~> d4.
Proof.
move=> a. 
pfold.
apply/rule_ctrans. apply/rule_cstar/rule_wrapinv. 
apply/rule_ctrans. apply/rule_drop.
apply/rule_ctrans. apply/rule_wrapinv.
apply/rule_ctrans. 2: { apply/rule_wrap. }
apply/rule_cplus. apply/rule_cid.
apply/rule_ctrans. apply/rule_assoc.
apply/rule_cseq. apply/rule_cid. (*Don't use rule_test yet*) (*apply/rule_test. left. pfold.*)

pfold_reverse. pcofix CIH. pfold. (*pcofix before cfix*)
apply/rule_cfix. simpl. 


apply/rule_ctrans. apply/rule_cseq. apply/rule_cid. apply/rule_dropinv.
apply/rule_ctrans. apply/rule_cseq. apply/rule_cid. apply/rule_cstar/rule_wrap. 

pfold_reverse. pcofix CIH2. pfold. (*pcofix before cfix*)
apply/rule_cfix. simpl. 



apply/rule_ctrans. apply/rule_cseq. apply/rule_wrapinv. apply/rule_cid.
apply/rule_ctrans. apply/rule_distR.
apply/rule_ctrans. apply/rule_cplus. apply/rule_proj. apply/rule_cid.
apply/rule_ctrans. 2: { apply/rule_drop. }
apply/rule_ctrans. 2: { apply/rule_wrap. }

(*Unset Printing Notations.*)
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
apply/rule_test. right. apply/CIH.

apply/rule_ctrans. apply/rule_assoc.
apply/rule_test. right. apply/CIH2.
Qed.


Print d4.


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

Fixpoint as_type (r : regex) : Type := 
match r with 
| Eps => unit 
| Empt => void
| Event a => { a' &  a' == a}
| Plus r0 r1 => (as_type r0) + (as_type r1)
| Seq r0 r1 => (as_type r0) * (as_type r1)
| Star r0 => seq (as_type r0)
end.

Parameter (l : seq (A * regex)).
Check (as_type (\big[Plus/Empt]_(i <- l) ((Event i.1) _;_ i.2))).

Definition dsl_in (d: dsl) : Type := 
match d with 
| shuffle => regex * regex * regex
| shuffleinv => regex * regex * regex
| retag => regex * regex
| _ =>  unit
end. 



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
fun r => match r in regex*regex*regex return _ => with (r0,r1,r2) => as_type ((r0 _+_ r1) _+_ r2) ->  as_type (r0 _+_ (r1 _+_ r2)) end
| shuffleinv => fun r => let: (r0,r1,r2) := r in  as_type (r0 _+_ (r1 _+_ r2))  -> as_type ((r0 _+_ r1) _+_ r2) 
| retag => fun r => let: (r0,r1):= r in  as_type (r0 _+_ r1)  -> as_type (r1 _+_ r0)
| _ =>  fun _ =>  A
end. 

Fixpoint dsl_type (d : dsl) : (dsl_in d)  -> Type := 
match d with 
| shuffle => fun r => match r in regex*regex*regex return _ => with (r0,r1,r2) => as_type ((r0 _+_ r1) _+_ r2) ->  as_type (r0 _+_ (r1 _+_ r2)) end
| shuffleinv => fun r => let: (r0,r1,r2) := r in  as_type (r0 _+_ (r1 _+_ r2))  -> as_type ((r0 _+_ r1) _+_ r2) 
| retag => fun r => let: (r0,r1):= r in  as_type (r0 _+_ r1)  -> as_type (r1 _+_ r0)
| _ =>  fun _ =>  A
end. 

Definition shuffle_i (r : regex * regex * regex) : (dsl_type shuffle r) :=
fun  T => 
match T with 
| inl (inl T') => inl T'
| inl (inr T') => inr (inl T')
| inr T' => inr (inr T')
end.

Check shuffle_i. Check (dsl_type shuffle).
Eval simpl in (dsl_in shuffle).

Definition shuffleinv_i r0 r1 r2  : (dsl_type shuffleinv r0 r1 r2) :=
fun  T => 
match T with 
| inl T' => inl (inl T')
| inr (inl T') => inl (inr T')
| inr (inr T') => (inr T')
end.

Definition retag_i r0 r1 r2 : (dsl_type retag r0 r1 r2) :=
fun T => 
match T with 
| inl T' => inr T' 
| inr T' => inl T'
end.

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
| shuffle => fun r0 r1 r2 =>  as_type ((r0 _+_ r1) _+_ r2) ->  as_type (r0 _+_ (r1 _+_ r2))
| shuffleinv => fun r0 r1 r2 =>  as_type (r0 _+_ (r1 _+_ r2))  -> as_type ((r0 _+_ r1) _+_ r2) 
| retag => fun r0 r1 => as_type (r0 _+_ r1)  -> as_type (r1 _+_ r0)
| _ =>  fun _ =>  A
end. 





Print plus. Print Nat.add.

Check interp.

Definition my_fix (l0 l1 : seq (A * regex))  (f : as_type r0 -> as_type r1) : 
  (as_type (\big[Plus/Empt]_(i <- l0) ((Event i.1) _;_ i.2))) ->
  (as_type (\big[Plus/Empt]_(i <- l1) ((Event i.1) _;_ i.2))) := 
 as_type ()
-> as_type r1  := 
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
