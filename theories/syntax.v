From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
From Containment Require Import  utils.

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

Notation "e _._ c" := (Seq (Event e) c)
                    (at level 51, right associativity).

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


(*Alternative Matching definition similar to isorecursive type inhabitation*)
Inductive Match2 : trace -> regex -> Prop :=
  | M2Eps : Match2 [::]  Eps
  | M2Event x : Match2 [::x] (Event x)
  | M2Seq s1 c1 s2 c2 :
             Match2 s1 c1 ->
             Match2 s2 c2 ->
             Match2 (s1 ++ s2) (c1 _;_ c2)
  | M2PlusL s1 c1 c2:
               Match2 s1 c1 ->
               Match2 s1 (c1 _+_ c2)
  | M2PlusR c1 s2 c2:
               Match2 s2 c2 ->
               Match2 s2 (c1 _+_ c2)
  | M2StarSeq c s :
                Match2 s (Eps _+_ (c _;_ (Star c))) ->
                Match2 s (Star c).
Hint Constructors Match2.

Lemma Match2P: forall s c, Match s c <-> Match2 s c.
Proof.
move => s c. split;first by elim;eauto.
elim;eauto.
move=> c0 s0 HM HM2. inv HM2.
inv H1. inv H1. con. done. done.
Qed.

Section axiomatization.
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
End axiomatization.
Hint Constructors c_eq.

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

Let eqs :=   (c_plus_neut_l,
             c_plus_neut,
             c_seq_neut_l,
             c_seq_neut_r,
             c_seq_failure_l,
             c_seq_failure_r,
             c_distr_l,
             c_distr_r,c_plus_idemp,plus_empt).


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
                  eauto.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  eauto.

Lemma co_eq_derive : forall (c0 c1 : regex) e, c0 =C= c1 -> e \ c0 =C= e \ c1.
Proof.
intros. pfold. punfold H. induction H; try solve [ simpl; rewrite ?eqs;eauto] . 
- simpl. case Hcase: (nu c0)=>//=. case Hcase1: (nu c1)=>//=. eauto. eauto.
- simpl;destruct (nu c);eauto. 
- simpl. destruct (nu c); eauto.
- simpl. destruct (nu c0); eauto. rewrite c_distr_l.
    eq_m_left. 
- simpl. destruct (nu c0); destruct (nu c1);simpl; auto. rewrite !c_plus_assoc !c_distr_r.
  eq_m_left. rewrite c_distr_r. eq_m_left. rewrite c_distr_r. eq_m_left.
- rewrite /= eqs. case Hcase:(nu _)=>/=.  rewrite c_plus_idemp //. done.
- rewrite /=. have: nu c0 = nu c0'. apply/c_eq_nu. eauto. move=>->.
  case Hcase:(nu _)=>//. apply/c_plus_ctx=>/=. apply/c_seq_ctx=>//. done. apply/c_seq_ctx=>//.
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

Definition o c := if nu c then Eps else Empt.
Transparent o.
Lemma o_plus : forall c0 c1 R, o (c0 _+_ c1) =(R)= o c0 _+_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto. rewrite eqs //.
Qed.

Lemma o_seq : forall c0 c1 R, o (c0 _;_ c1) =(R)= o c0 _;_ o c1.
Proof.
unfold o. intros. simpl. destruct (nu c0);destruct (nu c1);simpl;auto.
Qed.

Lemma o_true : forall c, nu c = true -> o c = Eps.
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
Qed.

Let o_eqs := (o_plus,o_seq,o_true,o_false).

(*Lemma enum_notin R: forall l a, a \notin l ->  a\ \big[Plus/Empt]_(i <- l) ((Event i)) =(R)= Empt.
Proof.
elim=>//. move=> a _/=. rewrite big_nil //.
move=> a l IH a0 //=. rewrite !inE.  move/andP=>[] Hneq Hin.
rewrite big_cons /=. rewrite eq_sym (negbTE Hneq) /= eqs //. apply/IH=>//.
Qed.

Lemma enum_in R: forall l a, a \in l ->  a\ \big[Plus/Empt]_(i <- l) ((Event i)) =(R)= Eps.
Proof.
elim=>//. 
move=> a l IH a0 //=. rewrite !inE. move/orP. case.
move/eqP=>Heq;subst. 
rewrite big_cons /= eqxx. 
case Hcase: (a \in l). rewrite IH //.
rewrite enum_notin // Hcase//.
move=> Hin. rewrite big_cons /=.
case: (eqVneq a a0). move=> Heq;subst.
rewrite IH //.
move=> Hneq. rewrite IH //=. rewrite eqs //.
Qed.

(************Summation rules used in showing normalization respects axiomatization*****)

Lemma enum_eps R: forall a, a\ \big[Plus/Empt]_(i : A) ((Event i)) =(R)= Eps.
Proof. move=> a. 
apply/enum_in. apply/mem_index_enum. 
Qed.*)


(*Lemma seq_derive_o : forall R e c0 c1, e \ (c0 _;_ c1) = (R) = e \ c0 _;_ c1 _+_ o (c0) _;_ e \ c1.
Proof.
intros;simpl.  destruct (nu c0) eqn:Heqn.
- destruct (o_destruct c0). rewrite H. eauto.
  unfold o in H. rewrite Heqn in H. discriminate.
- destruct (o_destruct c0). unfold o in H. rewrite Heqn in H. discriminate.
  rewrite H. eauto.
Qed.

Lemma seq_derive_o' : forall e c0 c1, e \ (c0 _;_ c1) =C= e \ c0 _;_ c1 _+_ o (c0) _;_ e \ c1.
Proof.
intros;simpl.  pfold. destruct (nu c0) eqn:Heqn.
- destruct (o_destruct c0). rewrite H. eauto.
  unfold o in H. rewrite Heqn in H. discriminate.
- destruct (o_destruct c0). unfold o in H. rewrite Heqn in H. discriminate.
  rewrite H. eauto.
Qed.*)

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

(*Lemma seq_derive_o_fun : forall R l c0 c1, \big[Plus/Empt]_(e0 <- l) (e0 \ (c0 _;_ c1)) =(R)= \big[Plus/Empt]_(e0 <- l)  (e0 \ c0 _;_ c1 _+_ o (c0) _;_ e0 \ c1).
Proof.
intros. under eq_big_plus => a Hin. 
rewrite seq_derive_o. over. rewrite //=.
Qed.*)


(*This has to be proved by induction because I cannot use ssreflects big_split since commutativity is over c_eq, and not leibniz equality*)
Lemma split_plus : forall R (B: eqType) l (P P' : B -> regex),
\big[Plus/Empt]_(a <- l) (P a _+_ P' a) = (R) = \big[Plus/Empt]_(a <- l) (P a) _+_ \big[Plus/Empt]_(a <- l) (P' a).  
Proof.
move => R B + P P'.
elim=>//. rewrite !big_nil // eqs //.
move=> a l IH. rewrite !big_cons. eq_m_left. rewrite IH. eauto.
Qed.


Lemma factor_seq_r : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (P a _;_ c) =(R)= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c.
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil eqs //.
move=> a l IH. rewrite !big_cons eqs //= IH //.
Qed.

(*Lemma factor_seq_l : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (c _;_ P a) =(R)=  c _;_ (\big[Plus/Empt]_(a <- l) (P a)).
Proof.
move=> R B +P c. elim=>//=. rewrite !big_nil eqs //.
move=> a l IH. rewrite !big_cons eqs //= IH //.
Qed.*)



(*Lemma enum_in2 R : forall (A : eqType) (P: A -> regex) l a, a\ \big[Plus/Empt]_(i <- l) (P i) =(R)=  \big[Plus/Empt]_(i <- l) (a \(P i)). 
Proof.
move=>B P.
elim=>//. move=> a. rewrite !big_nil //.
move=> a l IH a0 //=. rewrite !big_cons /=. eq_m_left.
Qed.

Lemma big_event_notin R : forall l a, a \notin l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(a \ Event i)) =(R)= Empt. 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //.
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite eq_sym (negbTE Hneq) IH // !eqs //.
Qed.




Lemma big_event_in R : forall l a, a \in l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(a \ Event i)) =(R)= Event a. 
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
Qed.*)

Lemma big_event_notin2 R : forall l a, a \notin l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) =(R)= Empt. 
Proof.
elim=>//=. move=> a _. rewrite !big_nil //.
move=> a l IH a0 /=. rewrite !inE. move/andP=>[] Hneq Hin.
rewrite !big_cons. rewrite (negbTE Hneq) IH // !eqs //.
Qed.

Lemma big_event_in2 R : forall l a, a \in l -> \big[Plus/Empt]_(i <- l) ((Event i)_;_(i \ Event a)) =(R)= Event a. 
Proof.
elim=>//=.
move=> a l IH a0 /=.
rewrite !inE. move/orP. case. move/eqP=>Heq;subst.
rewrite big_cons eqxx //= !eqs.
case Hcase: (a \in l). rewrite IH. apply/c_plus_idemp=>//. rewrite Hcase//.
rewrite big_event_notin2 //. rewrite Hcase//.
move=>Hin. rewrite big_cons IH //.
case: (eqVneq a a0). move=>Heq;subst. rewrite !eqs //.
move=>Hneq. rewrite !eqs //=.
Qed.

Lemma derive_unfold : forall R c, o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c) = (R) = c.
Proof.
move=>R. 
elim.
- rewrite /o /=. under eq_big_plus. move=> a Hin. rewrite !eqs. over. rewrite plus_empt eqs //.
- rewrite /o /=. under eq_big_plus. move=> a Hin. rewrite !eqs. over. rewrite plus_empt eqs //.
- move => s. rewrite big_event_in2 /o /=. rewrite eqs //. apply/mem_index_enum.
- move=> r HQ r' HQ'.  
  rewrite o_plus /=.
  under eq_big_plus. move=> a Hin. rewrite eqs. over. 
  rewrite split_plus. rewrite !c_plus_assoc. 
  rewrite [Plus (o r') _]c_plus_comm. rewrite c_plus_assoc. 
  rewrite [Plus  _ (o r')]c_plus_comm. rewrite HQ'. rewrite -c_plus_assoc HQ //.
- move=> r HQ r' HQ'. apply/c_trans. 2: { apply/c_seq_ctx. eauto. eauto. } 
  rewrite !eqs o_seq. 
  case Hcase:(nu r). 
  rewrite /o Hcase /= !eqs Hcase /=.
  under eq_big_plus. move=> a Hin. rewrite eqs. rewrite -c_seq_assoc. over.
  rewrite split_plus. rewrite factor_seq_r. 
  case Hcase':(nu _). rewrite !eqs.
  erewrite <- HQ'. rewrite eqs.
  rewrite /o Hcase'  /=. rewrite !eqs. eq_m_left.
  rewrite /= !eqs. 
  rewrite c_plus_comm. eq_m_left.  apply/c_seq_ctx. done. apply/c_sym. rewrite /o Hcase' eqs in HQ'. rewrite HQ'. done.

  rewrite /o Hcase /= !eqs Hcase /=.
  under eq_big_plus. move=> a Hin. rewrite -c_seq_assoc. over.
  rewrite factor_seq_r. 
  apply/c_trans. apply/c_seq_ctx. eauto. apply/c_sym. eauto. rewrite !eqs.
  case Hcase':(nu _); rewrite !eqs /o Hcase' !eqs //. 
- move=>r HQ /=. rewrite /o /=. apply/c_trans. 2 : { apply/c_star_ctx. eauto. }
  rewrite /o. case Hcase: (nu _). rewrite c_star_plus. 
  under eq_big_plus. move=> a Hin. rewrite -c_seq_assoc. over. rewrite factor_seq_r.

  apply/c_sym.
  rewrite -{1}c_unfold. eq_m_left. apply/c_seq_ctx. done.
  rewrite -c_star_plus. apply/c_trans. 2:{  apply/c_star_ctx. eauto. } 
  rewrite/o Hcase /=. done.
  rewrite eqs.
  apply/c_sym. rewrite -c_unfold. eq_m_left. apply/c_sym.
  under eq_big_plus. move=> a Hin. rewrite -c_seq_assoc. over. rewrite factor_seq_r.
  apply/c_seq_ctx. done. apply/c_trans. apply/c_sym. apply/c_star_ctx. eauto.
  rewrite /o Hcase /= eqs. done.
Qed.


Lemma big_shape: forall c, \big[Plus/Empt]_a (a _._ a \ c) = \big[Plus/Empt]_(i <- map (fun a => (a,a\c)) (index_enum A)) (i.1 _._ i.2).
Proof.
move=> c. move Heq: (index_enum _)=>ef. clear Heq.
elim: ef. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons /=. f_equal. done.
Qed.


Lemma bisim_completeness : forall c0 c1, Bisimilarity c0 c1 -> c0 =C= c1.
Proof.
pcofix CIH.
intros. punfold H0. inversion H0.
pfold. rewrite -(derive_unfold _ c0) -(derive_unfold _ c1). subst.
rewrite /o H2.
suff:    \big[Plus/Empt]_a (a _._ a \ c0) = (upaco2 c_eq r)=
  \big[Plus/Empt]_a (a _._ a \ c1). move=> HH.
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

End Regex.
