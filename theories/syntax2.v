From HB Require Import structures.


From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Relation_Definitions Setoid.

Require Import Paco.paco.
Require Import Coq.btauto.Btauto.
From Containment Require Import  utils.

Check Fix.



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
Inductive Match : trace -> regex -> Type :=
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

Definition equiv (r0 r1: regex) := forall s, (Match s r0 -> Match s r1)*(Match s r1 -> Match s r0).

Lemma seq_Eps : forall c, equiv (Eps _;_ c) c.
Proof.
move=> c s;split;intros. inversion X. inversion X0; subst. now simpl. by  apply/MSeq2;eauto.
Qed. 

Lemma seq_Empt : forall c, equiv (Empt _;_ c) Empt.
Proof.
move=> c s;split;intros. inversion X. inversion X0. inversion X.
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
- destruct (nu c1) eqn:Heqn; ssa.
- destruct (nu c1) eqn:Heq;ssa. apply/MSeq2. eauto. eauto. done.
Qed.



Lemma Match_nil_seq: forall c0 c1, Match nil (Seq c0 c1) -> (Match nil c0 * Match nil c1).
Proof.
move=> c0 c1 HM. inversion HM;subst. 
destruct s1;ssa. destruct s2;ssa.
Qed.

Lemma nuP : forall c, (nu c -> Match [::] c) * ( Match [::] c -> nu c) .
Proof.
move=> c. con;first by apply/Match_nil_nu=>//.
elim: c=>//=. move=> HM. inv HM. move=> s HM. inv HM.
move=> r IH r0 HM HM2. apply/orP. inv HM2;eauto.
move=> r IH r0 IH2 HM. apply/andP.
move/Match_nil_seq: HM=>[]. eauto.
Qed.

Lemma nuP1 : forall c, (nu c -> Match [::] c). 
Proof. intros. case: (nuP c);eauto. Qed.

Lemma nuP2 : forall c, (Match [::] c -> nu c). 
Proof. intros. case: (nuP c);eauto. Qed.


(*This direction with longer trace on the right because of induction step on trace*)
Lemma Match_matchb : forall (c : regex)(e : A)(s : trace), Match s (e \ c)-> Match (e::s) c.
Proof.
induction c;intros; simpl in*; try solve [inversion X].
- move: X. case Hcase:(_==_)=>// HM. rewrite (eqP Hcase).
  inv HM;auto. inv HM.
- inv X;eauto.
- destruct (nu c1) eqn:Heqn.
  * inv X.
    ** inv X0. apply/MSeq2;eauto.
    ** apply/MSeq2. apply/Match_nil_nu=>//. eauto. done.
  * inv X. apply/MSeq2. eauto. eauto. done.
- inversion X. apply/MStar2;eauto.
Qed.




Theorem  matchbP: forall (c : regex)(s : trace), (Match s c -> matchb s c) *   (matchb s c -> Match s c) . 
Proof.
move=> c s. rewrite /matchb.
split;first by apply/Match_i_matchb=>//.
elim: s c=>//;first by move=> c /Match_nil_nu=>//.
move=> a l IH c /=. move/IH/Match_matchb=>//.
Qed.

Theorem  matchbP1: forall (c : regex)(s : trace), (Match s c -> matchb s c).   
Proof.  intros. case: (matchbP c s)=>//. eauto. Qed.

Theorem  matchbP2: forall (c : regex)(s : trace), (matchb s c -> Match s c). 
Proof. intros. case: (matchbP c s)=>//. eauto. Qed.

(*Inconvenient I cannot rewrite*)
Lemma deriveP : forall (c : regex)(e : A)(s : trace), (Match (e::s) c -> Match s (e \ c)) *  ( Match s (e \ c) -> Match (e::s) c) .
Proof.
move=> c e s. con;intros. 
apply/((matchbP _ _).2). move/((matchbP _ _).1) : X=>//.
apply/((matchbP _ _).2). move/((matchbP _ _).1) : X=>//.
Qed.

Lemma deriveP1 : forall (c : regex)(e : A)(s : trace), (Match (e::s) c -> Match s (e \ c)).
Proof. intros. case: (deriveP c e s)=>//. eauto. Qed.

Lemma deriveP2 : forall (c : regex)(e : A)(s : trace), ( Match s (e \ c) -> Match (e::s) c) .
Proof. intros. case: (deriveP c e s)=>//. eauto. Qed.


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

Set Printing Universes.
Inductive bisimilarity_gen bisim : regex -> regex -> Type :=
 bisimilarity_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Type ) (H1: nu c0 == nu c1 : Type) : bisimilarity_gen bisim c0 c1.


Inductive bot2T {A : Type} : A -> A -> Set :=.

CoInductive Testt : regex -> regex -> Type := 
| TT r0 r1 : bisimilarity_gen Testt r0 r1 -> Testt r0 r1.
Check paco2. Check bisimilarity_gen.

Check paco2.

Inductive SomeF rel : nat -> nat -> Type := Con n0 n1 : rel n0 n1 -> SomeF rel n0 n1.

Definition Bisimilarity := paco2 SomeF.
Hint Unfold  Bisimilarity : core.

Lemma bisimilarity_gen_mon: monotone2 bisimilarity_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve bisimilarity_gen_mon : paco.

(*Print equiv.
Definition equiv_r (r0 r1 : regex) := forall s, Match s r0 <-> Match s r1.*)

Theorem equiv_r1 : forall c0 c1, equiv c0 c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  intro. con. move/deriveP2=>HH =>/=. apply/deriveP1. 
  edestruct X. eauto.
  move/deriveP2=>HH =>/=. apply/deriveP1. 
  edestruct X. eauto.
  apply/eq_iff. con. move/nuP1=>HH. apply/nuP2. 
  edestruct X. eauto. move/nuP1=>HH. apply/nuP2. edestruct X. eauto.
Qed.

Theorem equiv_r2 : forall c0 c1, Bisimilarity c0 c1 -> equiv c0 c1. 
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


Section DSL.


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
Arguments Co_build {A B}.


Inductive star (A : Type) := 
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
end. 
Notation "c0 <T= c1" := ((as_type c0) -> (as_type c1))(at level 63).
Notation "c0 <O= c1" := ((as_type c0) -> option (as_type c1))(at level 63).

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Definition shuffle_i A B C : (A _+_ B) _+_ C <T= A _+_ (B _+_ C) :=
fun  T => 
match T with 
| inl (inl T') => inl T'
| inl (inr T') => inr (inl T')
| inr T' => inr (inr T')
end.

Definition shuffleinv_i A B C :  A _+_ (B _+_ C)  <T= (A _+_ B) _+_ C :=
fun  T => 
match T with 
| inl T' => inl (inl T')
| inr (inl T') => inl (inr T')
| inr (inr T') => (inr T')
end.

Definition retag_i A B : A _+_ B <T= B _+_ A :=
fun T => 
match T with 
| inl T' => inr T' 
| inr T' => inl T'
end. 

Definition untagL_i A : Empt _+_ A <T= A :=
fun T => 
match T with 
| inl T' => match T' with end 
| inr T' => T' 
end.

Definition untagLinv_i {A} : A <T= Empt _+_ A :=
fun T => inr T.

Definition untag_i A : A _+_ A <T= A :=
fun T =>
match T with 
| inl T' => T'
| inr T' => T'
end.

Definition tagL_i {A B} :  A <T= (A _+_ B ) := inl.

Definition assoc_i A B C : ((A _;_ B) _;_ C)<T=  (A _;_ (B _;_ C)) := 
fun T => let: ((T0,T1),T2) := T in (T0,(T1,T2)).

Definition associnv_i A B C : (A _;_ (B _;_ C)) <T=  ((A _;_ B) _;_ C) :=
fun T => let: (T0,(T1,T2)) := T in ((T0,T1),T2).

Definition swap_i A :  (A _;_ Eps)<T=  (Eps _;_ A) := fun T => (tt,T.1).
Definition swapinv_i A : (Eps _;_ A) <T= (A _;_ Eps) := fun T => (T.2,tt).

Definition proj_i A : (Eps _;_ A)<T=  A := snd.
Definition projinv_i {A} : A <T= (Eps _;_ A) := fun T => (tt,T).

Definition abortR_i A : (A _;_ Empt) <T=  Empt := fun T => match T.2 with end.
Definition abortRinv_i A : Empt  <T=  (A _;_ Empt) := fun T => match T with end.

Definition abortL_i A : (Empt _;_ A) <T=  Empt := fun T => match T.1 with end.
Definition abortLinv_i A : Empt <T=   (Empt _;_ A) := fun T => match T with end.

Definition distL_i A B C : (A _;_ (B _+_ C)) <T= ((A _;_ B) _+_ (A _;_ C)) := 
fun T => let: (T0,T1) := T in 
match T1 with 
| inl T' => inl (T0,T')
| inr T' => inr (T0,T')
end.
Definition distLinv_i A B C :  ((A _;_ B) _+_ (A _;_ C)) <T= (A _;_ (B _+_ C)) :=
fun T => 
match T with 
| inl (T0,T1) => (T0,inl T1)
| inr (T0,T1) => (T0,inr T1)
end.

Definition distR_i A B C : ((A _+_ B) _;_ C) <T=  ((A _;_ C) _+_ (B _;_ C)) :=
fun T => let: (T0,T1) := T in 
match T0 with 
| inl T' => inl (T',T1)
| inr T' => inr (T',T1)
end.
Definition distRinv_i A B C : ((A _;_ C) _+_ (B _;_ C))  <T= ((A _+_ B) _;_ C) :=
fun T => 
match T with 
| inl (T0,T1) => (inl T0,T1)
| inr (T0,T1) => (inr T0,T1)
end.

Definition wrap_i A : (Eps _+_ (A _;_ Star A)) <T= (Star A) := fold_s.
(*fun T => 
match T with
| inl _ => nil 
| inr (T0,T1) => cons T0 T1
end.*)
Definition wrapinv_i A : (Star A) <T= (Eps _+_ (A _;_ Star A)) := unfold_s.
(*fun T => 
match T with 
| nil => inl tt
| cons a T' => inr (a,T')
end.*)
Fixpoint drop_i A :  (Star (Eps _+_ A)) <T= (Star A) :=
fix drop_i T := 
match unfold_s T with
| inl _ => fold_s (inl tt)
| inr (a,T') => match a with | inl tt => fold_s (inl tt) | inr a' => fold_s (inr (a',drop_i T')) end
end.

Definition dropinv_i A : (Star A) <T= (Star (Eps _+_ A)) :=
fix dropinv_i T := 
match unfold_s T with 
| inl _ => fold_s (inl tt)
| inr (a,T') => fold_s (inr (inr a,dropinv_i T'))
end.

Definition cid_i {c} : c <T= c := fun x => x.


Definition cseq_i A A' B B'  (f0 : A <T=  A') (f1 : B <T= B') : (A _;_ B) <T= (A' _;_ B') :=
fun T => let: (T0,T1) := T in (f0 T0, f1 T1).

Definition cstar_i A B (f : A <T= B) : (Star A)  <T= (Star B) := 
fix cstar_i T := 
match unfold_s T with 
| inl _ => fold_s (inl tt)
| inr (a,T') => fold_s (inr (f a,(cstar_i T')))
end.

Definition ctrans_i A B C (f : A <T=B) (f' :B <T=C) :  A <T=C :=
f' \o f.

Definition cplus_i A B A' B' (f :  A <T=A' ) (f' :  B <T=B' ) : A _+_ B <T=A' _+_ B' :=
fun T => 
match T with 
| inl T' => inl (f T')
| inr T' => inr (f' T')
end.




Definition shuffle_o A B C : (A _+_ B) _+_ C <O= A _+_ (B _+_ C) := Some \o shuffle_i.  
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
| inl _ => Some (fold_s (inl tt))
| inr (a,T') => if (f a,cstar_i T') is (Some b,Some T') then Some (fold_s (inr (b,(T')))) else None
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
| inl T' => omap inl (f T')
| inr T' => omap inr (f' T')
end.

Definition guard_o {a c0 c1} (f : c0 <O= c1) : ((Event a) _;_ c0) <O= ((Event a) _;_ c1) := 
fun T => let: (a,T') := T in if f T' is Some T'' then Some (a,T'') else None.

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

Definition nu_as_type (r : regex) (H : nu r) : (as_type r).
move: (to_Nu _ H). clear H.
elim=>//.
move => c c' Hnu T. apply/inl. done.
move=> c c' Hnu T. apply/inr. done.
move=> c. apply/fold_s. left. con.
Defined.

(*We use a unfolding rule that let's Coq produce an induction principle we can use*)
Inductive typing : forall r, as_type r -> Type := 
| T0 : typing Eps tt
| T1 (a : A)  : typing (Event a) (build_single _ a)
| T2 a : typing Empt a
| T3 r0 r1 T : typing r0 T -> typing (Plus r0 r1) (inl T)
| T4 r0 r1 T : typing r1 T -> typing (Plus r0 r1) (inr T)
| T5 r0 r1 T0 T1 : typing r0 T0 -> typing r1 T1 -> typing (Seq r0 r1) (T0, T1)
| T6 c T : typing Eps T -> typing (Star c) (fold_s (inl T))
| T7 c T : typing (c _;_ (Star c)) T -> typing (Star c) (fold_s (inr T)).

Hint Constructors typing.

Definition normalize (r : regex) : r <T= (o r) _+_ \big[Plus/Empt]_(i <- l) <

Lemma all_types : forall (r : regex) (T : as_type r), typing r T. 
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
rewrite /as_type /=.   case0> inv T.
Fixpoint reg_size {r : regex} := 
fun T => let f := as_type in 
match r as r' return as_type r' -> nat with 
| Eps => fun _ => 0
| Empt => fun T => match T with end
| Event _ => fun _ => 1
| Plus r0 r1 => fun T => match T with 
                     | inl T' => @reg_size r0 T'
                     | inr T' => @reg_size r1 T'
                     end
| Seq r0 r1 => fun T => let: (T0,T1) := T in (@reg_size r0 T0) + (@reg_size r1 T1)
| Star r0 => fun T => match unfold_s T with 
                    | inl _ => 0 
                    | inr (T0,T1) => (@reg_size r0 T0) + (@reg_size (Star r0) T1)
                  end
end T.


Fixpoint flatten (n : nat) (r : regex) {struct n} : as_type r -> option (seq A) := 
if n is n'.+1 then
match r as r' return as_type r' -> option (seq A) with 
| Eps =>  fun _ => Some nil 
| Empt => fun T => match T with end 
| Event a => fun _ => Some (a::nil)
| Plus r0 r1 => fun T => match T with | inl T' => flatten n' r0 T' | inr T' => flatten n' r1 T' end
| Seq r0 r1 => fun T => let: (T0,T1) := T in obind (fun l => obind (fun l' => Some (l++l')) (flatten n' r1 T1)) (flatten n' r0 T0)
| Star r0 => fun T => match unfold_s T with 
                   | inl _ => Some nil
                   | inr (t,T') => obind (fun l => obind (fun l' => Some (l ++ l')) (flatten n' (Star r0) T')) (flatten n' r0 t)  
                  end 
end
else fun _ => None.

Fixpoint tree_size {r : regex} := 
fun T => let f := as_type in 
match r as r' return as_type r' -> nat with 
| Eps => fun _ => 0
| Empt => fun T => match T with end
| Event _ => fun _ => 1
| Plus r0 r1 => fun T => match T with 
                     | inl T' => @reg_size r0 T'
                     | inr T' => @reg_size r1 T'
                     end
| Seq r0 r1 => fun T => let: (T0,T1) := T in (@reg_size r0 T0) + (@reg_size r1 T1)
| Star r0 => fun L => foldr (fun x acc => (@reg_size r0 x) + acc) 0  L 
end T.


Definition tree_of_match (s : trace) (r : regex) (H : matchb s r) : (as_type r).
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

Fixpoint tree_of_match (s : trace) (r : regex) (H : Match s r) : option (as_type r) := 
match H in Match s r return option (as_type r) with 
| MEps => Some tt
| _ => None
end.



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

(*Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.*)

(*Inductive dsl3 :  Set := 
| shuffle3  : regex-> dsl3. ((A _+_ B) _+_ C) (A _+_ (B _+_ C)).
| ctrans3 (A B C: regex) : dsl3 R A B -> dsl3 R B C -> dsl3 R A C
| cplus3 (A B C D: regex) : dsl3 R A B -> dsl3 R C D -> dsl3 R (A _+_ C) (B _+ D)
| guard3 (A B : regex) : R A B -> dsl3 R A B.*)






Fixpoint interp (r0 r1 : regex)
           (d : dsl2 dsl_co r0 r1)  (f : forall x y, dsl_co x y -> x <O= y ) :  r0 <O= r1 :=
match d in dsl2 _ r0 r1 return (as_type r0) -> option (as_type r1) with 
| @cid2 _ A => (@cid_o A)
| @shuffle2 _ A B C => (@shuffle_o A B C)
| @shuffleinv2 _ A B C => (@shuffleinv_o A B C)
| @ctrans2 _ A B C d0 d1 => (@ctrans_o A B C) (@interp _ _ d0 f) (@interp _ _ d1 f)
| @cplus2 _ A B C D d0 d1 => (@cplus_o A B C D (@interp _ _ d0 f)) (@interp _ _ d1 f)
| @guard2 _ a A B pco => guard_o (f _ _ pco)
end.

Fixpoint interp_wrap (n : nat) (r0 r1 : regex) (d : dsl_co r0 r1) : r0 <O= r1 :=
match d in dsl_co x y return x <O= y  with 
          | Co_build _ _ dco => if n is n'.+1 then interp dco (interp_wrap n') else fun _ => None
end. 



Lemma fix_eq : forall n, ((fix interp_wrap (n0 : fin) (r0 r1 : regex) (d0 : dsl_co r0 r1) {struct n0} : r0 <O= r1 := match d0 in (dsl_co x y) return (x <O= y) with
                                                                                                | @Co_build A1 B0 dco => match n0 with
                                                                                                                         | 0 => fun=> None
                                                                                                                         | n'.+1 => interp dco (interp_wrap n')
                                                                                                                         end
                                                                                                end) n) = interp_wrap n.
Proof. done. Qed.

Lemma interp_wrap_unf : forall n r0 r1 (d : dsl_co r0 r1), interp_wrap n.+1 d = match d in dsl_co x y return x <O= y  with 
          | Co_build _ _ dco => interp dco (interp_wrap n) end.
Proof. move => n r0 r1 d //=. 
Qed.

(*Require Import Coq.Program.Equality.*)
(*Check interp.
Lemma interp_wrap0 : forall r0 r1 (d : dsl2 dsl_co r0 r1), interp d (interp_wrap 0) = fun _ => None.
Proof.
move => r0 r1 d. fext. move=> x. 
elim: d x=>//.
rewrite /interp_wrap. case: d=>//.
Qed.*)

Lemma interp_trans : forall r0 r1 r2  (f : forall x y, dsl_co x y -> x <O= y) (d : dsl2 dsl_co r0 r1) (d' : dsl2 dsl_co r1 r2) T, interp (ctrans2 d d') f T -> interp d f T.
Proof.
move=> r0 r1 r2 f d d' T. rewrite /= /ctrans_o /obind /oapp /=. case: (interp _ _ _)=>//.
Qed.


Lemma interp_trans2 : forall r0 r1 r2  (f : forall x y, dsl_co x y -> x <O= y)  (d : dsl2 dsl_co r0 r1) (d' : dsl2 dsl_co r1 r2) T T', interp (ctrans2 d d') f T -> interp d f T = Some T' -> interp d' f T'.
Proof.
move => r0 r1 r2 Hf d d' T T' /= + Hsome. rewrite /= /ctrans_o /obind /oapp /=. rewrite Hsome //.
Qed.

Lemma as_type_eq : forall (A0 : regex), (fix as_type (r : regex) : Type := match r with
                                           | Eps => unit
                                           | Empt => void
                                           | Event a => {a' : A & a' == a}
                                           | r0 _+_ r1 => (as_type r0 + as_type r1)%type
                                           | r0 _;_ r1 => (as_type r0 * as_type r1)%type
                                           | Star r0 => seq (as_type r0)
                                           end) A0 = as_type A0.
Proof. done. Qed.

Lemma reg_size1 : forall a (T : as_type (Event a)), @reg_size (Event a) T = 1.
Proof.
move=> a T. rewrite /reg_size //.
Qed.

Lemma interp_ineq : forall A B (d : dsl2 dsl_co A B) (T : as_type A) (T' : as_type B) (f : forall x y, dsl_co x y -> x <O= y), (forall x y (dco : dsl_co x y) (T0 : as_type x) (T1 : as_type y) , f x y dco T0 = Some T1 -> reg_size T1 <= reg_size T0) ->  
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
Lemma interp_wrap_ineq : forall n A B (d : dsl_co A B) (T : as_type A) (T' : as_type B),  interp_wrap n d T = Some T' -> reg_size T' <= reg_size T.
Proof.
elim.
- move=> A0 B [] //=.
- move=> n IH A0 B [] T T' d T0 T0'. rewrite interp_wrap_unf. move=> Hint.  apply/interp_ineq;last by eauto. 
  move=> x y dco T1 T2 Hin. eauto.
Qed.


Lemma interp_some : forall A B (f : forall x y, dsl_co x y -> x <O= y) (d : dsl2 dsl_co A B) (T : as_type A) , (forall x y (dco : dsl_co x y) (T0 : as_type x), f x y dco T0) ->  
                                                                                                                    interp d f T.
Proof.
move=> A' B f. 
- elim=>//. 
(* *  move=> B0 T0 T1 /=. rewrite /cid_o. case=>//->//.
 * move => A0 B0 C T T' /=. rewrite /shuffle_o /shuffle_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C T T' /=. rewrite /shuffleinv_o /shuffleinv_i /=. case=><-. case: T=>//. by case.*)
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


(*Lemma interp_ineq : forall A B (d : dsl2 dsl_co A B) (T : as_type A) (T' : as_type B) n, interp d (interp_wrap n) T = Some T' -> reg_size T' <= reg_size T.
Proof.
move=> A' B. 
- elim=>//.
 *  move=> B0 T0 T1 _ /=. rewrite /cid_o. case=>//->//.
 * move => A0 B0 C T T' _ /=. rewrite /shuffle_o /shuffle_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C T T' _ /=. rewrite /shuffleinv_o /shuffleinv_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C d IH d0 IH2 T T' n Hsome. 
   have: interp (ctrans2 d d0) (interp_wrap n) T by rewrite Hsome//. 
   move/[dup]=>Tsome. move/interp_trans.
   case Heq: (interp _ _ _)=>// [T''] _. move: (IH _ _ _ Heq)=>Hsize. 
   move/interp_trans2: (Heq). move/(_ _ d0 Tsome).
   case Heq2: (interp _ _ _)=>// [T'''] _. move: (IH2 _ _ _ Heq2). 
   move=> Hsize2.
   move: Hsome. rewrite /= /ctrans_o /= /obind /oapp /= Heq Heq2.
   case. move=> HT;subst. lia.
 * move=> A0 B0 C D d IH d0. move=> IH2 T T'  n/=. rewrite /cplus_o /=. 
   case: T. 
  **  move=> T2. rewrite /omap /obind /oapp. 
      case Heq: (interp _ _ _) => // [T3 ]. case. move=> HT3;subst. apply/IH. eauto. 
  **  move=> T2. rewrite /omap /obind /oapp. 
      case Heq: (interp _ _ _) => // [T3 ]. case. move=> HT3;subst. apply/IH2. eauto. 
 * move => A0 B0 r T T' /=.  destruct r=>//.
- move=> n IH d T T'. rewrite /=. 
*)

(*Lemma interp_ineq : forall A B n (d : dsl2 dsl_co A B) (T : as_type A) (T' : as_type B), interp d (interp_wrap n) T = Some T' -> reg_size T' <= reg_size T.
Proof.
move=> A' B. elim=>//.
- move=> d T T'. 
  elim: d T T'=>//.
 *  move=> B0 T0 T1 /=. rewrite /cid_o. case=>//->//.
 * move => A0 B0 C T T' /=. rewrite /shuffle_o /shuffle_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C T T' /=. rewrite /shuffleinv_o /shuffleinv_i /=. case=><-. case: T=>//. by case.
 * move=> A0 B0 C d IH d0 IH2 T T' Hsome. 
   have: interp (ctrans2 d d0) (interp_wrap 0) T by rewrite Hsome//. 
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
      case Heq: (interp _ _ _) => // [T3 ]. case. move=> HT3;subst. apply/IH. done.
  **  move=> T2. rewrite /omap /obind /oapp. 
      case Heq: (interp _ _ _) => // [T3 ]. case. move=> HT3;subst. apply/IH2. done.
 * move => A0 B0 r T T' /=.  destruct r=>//.
- move=> n IH d T T'. rewrite /=. 

case Hcase: (interp _ _ _)=>// [T2]. case=>HT2;subst.
  apply/IH.  eauto.
move => Hin. apply/IH.
 case Hcase: r.
  **
rewrite fix_eq.
 move.
lia.
 Tsome).
   move: (interp_trans2 _ _ _ _ _ _ _ _ Tsome Heq).

   
suff: reg_size T <= reg_size T'' by lia.
move/[dup]. move/interp_transp.
   rewrite /interp.
C T T' /=. rewrite /shuffleinv_o /shuffleinv_i /=. case=><-. case: T=>//. by case.

 rewrite /shuffle_i //. 
   move
destruct T,T';ssa. destruct a;ssa.
 case: T=>//.
rewrite interp_wrap0.

d T T' n Hsome.
 as_type A1
  Hsize : reg_size A1 T < n.+1
  T' : as_type B0
  Heq : interp d (interp_wrap n) T = Some T'
*)

(*Lemma interp_wrap_some : forall n r0 r1 (d : dsl_co r0 r1) (T : as_type r0), reg_size T < n -> { T' | interp_wrap n d T = Some T'}.
Proof.
elim.
- move=> r0 r1 d T // Hsize.  
- move => n IH r0 r1 d T Hsize /=. destruct d.
  elim: d T Hsize IH=>//.
 * move=> B0 T Hsize IH. 
 move=> B0. C d IH d0 IH2 T Hsize IH3 /=. rewrite /ctrans_o /obind /oapp /=.
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
Qed.*)

Lemma interp_wrap_some : forall n r0 r1 (d : dsl_co r0 r1) (T : as_type r0), reg_size T < n -> interp_wrap n d T.
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

Lemma interp_wrap_sig : forall n r0 r1 (d : dsl_co r0 r1) (T : as_type r0), reg_size T < n -> { T' | interp_wrap n d T = Some T'}.
Proof.
move=> n r0 r1 d T Hsize.
move: (interp_wrap_some  n d T Hsize). case Hcase: (interp_wrap n d T)=>// [T'] _. econ. eauto.
Qed.

Lemma size_proof : forall (r : regex) (T : as_type r), leq ((reg_size T)) (reg_size T). done. Defined.

Definition interp_total (r0 r1 : regex) (d : dsl_co r0 r1) := 
fun T =>
match interp_wrap_sig (reg_size T).+1 d T (size_proof r0 T) with
| exist T' _ => T'
end.


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
Fixpoint interp (d : dsl2) : (as_type (from d)) -> (as_type (to d)) :=
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
| inl (inl T') => inl T'
| inl (inr T') => inr (inl T')
| inr T' => inr (inr T')
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
