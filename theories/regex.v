From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Containment.tactics.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Let inE := tactics.inE.

Section Regex.
Variable (A : eqType).
Inductive regex  : Type :=
| Eps : regex
| Empt : regex
| Event : A -> regex
| Plus : regex -> regex -> regex
| Seq : regex -> regex -> regex
| Star : regex -> regex.

Definition regex_indDef := [indDef for regex_rect].
Canonical regex_indType := IndType regex regex_indDef.

Definition regex_hasDecEq := [derive hasDecEq for regex].
HB.instance Definition _ := regex_hasDecEq.


Notation "c0 _;_ c1"  := (Seq c0 c1)
                         (at level 52, left associativity).

Notation "c0 _+_ c1"  := (Plus c0 c1)
                         (at level 53, left associativity).
Definition trace := seq A.

Fixpoint nu(c:regex ):bool :=
match c with
| Eps => true
| Empt => false
| Event e => false
| Seq c0 c1 => nu c0 && nu c1
| Plus c0 c1 => nu c0 || nu c1
| Star c => true
end.

Inductive Match : trace -> regex -> Prop :=
  | MEps : Match [::]  Eps
  | MEvent x : Match [::x] (Event x)
  | MSeq s1 c1 s2 c2 : Match s1 c1 ->  Match s2 c2 -> Match (s1 ++ s2) (c1 _;_ c2)
  | MPlusL s1 c1 c2:  Match s1 c1 -> Match s1 (c1 _+_ c2)
  | MPlusR c1 s2 c2:  Match s2 c2 ->  Match s2 (c1 _+_ c2)
  | MStar0 c  : Match [::] (Star c)
  | MStarSeq c s1 s2:  Match s1 c -> Match s2 (Star c) -> Match (s1 ++ s2) (Star c).
Hint Constructors Match.

Definition equiv (r0 r1: regex) := forall s, Match s r0 <-> Match s r1.


Lemma MSeq2: forall s0 s1 c0 c1 s, Match s0 c0 -> Match s1 c1 -> s = s0 ++ s1  -> Match s (c0 _;_ c1).
Proof.
move => s0 s1 c0 c1 s HM0 HM1 Heq;subst. eauto.
Qed.

Lemma MStar2 : forall s0 s1 c s, Match s0 c -> Match s1 (Star c) -> s = s0 ++ s1  -> Match s (Star c).
Proof.
move => s0 s1 c s HM0 HM1 Heq;subst. eauto.
Qed.



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

Reserved Notation "s \\ c" (at level 42, no associativity).
Fixpoint trace_derive (s : trace) (c : regex)  : regex :=
match s with
| [::] => c
| e::s' => s' \\ (e \ c)
end
where "s \\ c" := (trace_derive s c).

Lemma derive_distr_plus : forall (s : trace)(c0 c1 : regex), s \\ (c0 _+_ c1) = s \\ c0 _+_ s \\ c1.
Proof.
induction s;intros;simpl;auto.
Qed. 

Hint Rewrite derive_distr_plus.


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

Fixpoint pd a r := 
match r with 
| Eps => nil 
| Empt => nil 
| Event a' => if a == a' then Eps::nil else nil
| Plus r0 r1 => (pd a r0) ++ (pd a r1)
| Seq r0 r1 => if nu r0 then (map (fun x => Seq x r1) (pd a r0)) ++ (pd a r1) else (map (fun x => Seq x r1) (pd a r0))
| Star r0 => map (fun x => x _;_ Star r0) (pd a r0)
end.

(*uniqueness of pd_l will become important later for decision procedure*)
Definition pd_l a l := undup (flatten (map (pd a) l)).
Definition pd_sum a r := \big[Plus/Empt]_(r <- (pd a r)) r.
Definition pder := seq regex.

Lemma Match_big_undup : forall l s, Match s (\big[Plus/Empt]_(i <- undup l) i)  <->  Match s ((\big[Plus/Empt]_(i <- l) i)).
Proof.
elim;ssa. case_if. rewrite !big_cons. split.
move/H. eauto. intros. apply/H. inv H1;eauto. 
clear H1 H.
elim: l a H0 H4;ssa.  rewrite !inE in H0. de (orP H0). norm_eqs. rewrite big_cons. eauto. 
rewrite big_cons. eauto. 
rewrite !big_cons. split. intros. inv H1;eauto. constructor 5. apply/H. done.
intros. inv H1;eauto. constructor 5. apply/H. done.
Qed.

Lemma Match_big_cat : forall l  l' s, Match s (\big[Plus/Empt]_(i <- l ++ l') i)  <->  Match s ((\big[Plus/Empt]_(i <- l) i) _+_  (\big[Plus/Empt]_(i <- l') i)).
Proof.
split.
elim: l l' s. ssa. 
move=> a l IH l' s.  rewrite /= !big_cons. intros. inv H. eauto.
apply IH in H2. inv H2. eauto. eauto.
elim: l l' s. ssa. rewrite big_nil in H.  inv H. inv H2.
move=> a l IH l' s.  rewrite /= !big_cons. intros. inv H. inv H2. eauto. 
constructor 5.
apply:IH. eauto. eauto.
Qed.

Lemma Match_factor_r : forall l s r (F : regex -> regex), Match s (\big[Plus/Empt]_(i <- l) (F i _;_ r)) -> Match s (\big[Plus/Empt]_(i <- l) (F i) _;_ r). 
Proof.
elim;ssa. rewrite big_nil in H. inv H.
move: H0. rewrite !big_cons. intros. inv H0. inv H3. eauto. 
apply H in H3. inv H3. eauto.
Qed.


Lemma Match_factor_r2 : forall l s r (F : regex -> regex),  Match s (\big[Plus/Empt]_(i <- l) (F i) _;_ r) -> Match s (\big[Plus/Empt]_(i <- l) (F i _;_ r)). 
Proof.
elim;ssa. rewrite big_nil in H. inv H. inv H3.
move: H0. rewrite !big_cons. intros. inv H0. inv H4. eauto. eauto.
Qed.



Lemma map_big_plus : forall l (f : regex -> regex), 
\big[Plus/Empt]_(a <- map f l) a = \big[Plus/Empt]_(a <- l) (f a).
Proof.
elim;ssa.
rewrite !big_nil. done.
rewrite !big_cons. f_equal. done.
Qed.

Lemma has_nu_Match : forall l, Match [::] (\big[Plus/Empt]_(i <- l) i) ->  has nu l.
Proof.
elim;ssa. rewrite big_nil in H. inv H.
rewrite !big_cons in H0. inv H0. 
left. rewrite matchbP /matchb // in H3. eauto.
Qed.

Lemma Match_has_nu : forall l, has nu l ->  Match [::] (\big[Plus/Empt]_(i <- l) i).
Proof.
elim;ssa. de (orP H0). rewrite !big_cons /=. con.
apply:Match_nil_nu. done.
rewrite !big_cons. constructor 5. eauto.
Qed.

Lemma Match_has_nu_iff : forall l, has nu l <->  Match [::] (\big[Plus/Empt]_(i <- l) i).
Proof.
intros. split. apply/Match_has_nu. apply/has_nu_Match.
Qed.

Lemma der_eq : forall e r s, Match s (derive e r) <-> Match s (pd_sum e r).
Proof.
intros. rewrite /pd_sum. split.
elim: r s e;ssa.  rewrite big_nil //. rewrite big_nil //.
move: H. case_if. norm_eqs. rewrite eqxx. rewrite !big_cons big_nil. eauto.
rewrite eq_sym H big_nil //=.
inv H1. apply H in H4.
move: H4. move: (pd e r0)=> l. 
intros. apply/Match_big_cat. eauto.
apply H0 in H4. apply/Match_big_cat. eauto.
destruct (nu _) eqn:Heqn.  
apply/Match_big_cat.  inv H1.  inv H4. 
con.
apply H in H6. 
rewrite map_big_plus. apply Match_factor_r2. eauto. eauto. 
inv H1.  apply H in H5.
rewrite map_big_plus. apply Match_factor_r2. eauto.
inv H0. rewrite map_big_plus. apply Match_factor_r2. eauto.

rewrite /pd_sum.
elim: r s e;ssa.  rewrite big_nil // in H. rewrite big_nil // in H.
move: H. case_if. norm_eqs. rewrite eqxx. rewrite !big_cons big_nil. intros. inv H. inv H2. 
rewrite eq_sym H big_nil //=. apply Match_big_cat in H1. inv H1. eauto. eauto.
destruct (nu _) eqn:Heqn.  apply Match_big_cat in H1. inv H1. 
rewrite map_big_plus in H4. apply Match_factor_r in H4. inv H4. eauto. eauto.
rewrite map_big_plus in H1. apply Match_factor_r in H1. inv H1. eauto. 
rewrite map_big_plus in H0. apply Match_factor_r in H0. inv H0. eauto.
Qed.

Lemma deriveP2
     : forall (c : regex) (e : A) (s : trace),
       Match (e :: s) c <-> Match s (pd_sum e  c).
Proof. intros. 
rewrite -der_eq. apply/deriveP.
Qed.


Lemma pd_plus : forall l e, undup (pd e (\big[Plus/Empt]_(i <- l) i)) = pd_l e l.
Proof.
rewrite /pd_l.
elim;ssa.
rewrite big_nil. done.
rewrite big_cons /=. rewrite !undup_cat.  f_equal;try done. 
apply/eq_in_filter. intro. ssa.   clear H0.
move: x. clear H.  elim: l. ssa. rewrite big_nil. done. 
intros. rewrite !big_cons /=.
rewrite !mem_cat !negb_or. f_equal. eauto.
Qed.

Definition equiv_r (r0 r1 : regex) := forall s, Match s r0 <-> Match s r1.
Definition contains_r (r0 r1 : regex) := forall s, Match s r0 -> Match s r1.


End Regex.
Arguments regex {A}.
Arguments pder {A}.
Arguments trace {A}.
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







(*Lemma nu_seq_derive : forall (e : A)(c0 c1 : regex), 
nu c0 -> nu (e \ c1) -> nu (e \ (c0 _;_ c1)).
Proof.
intros. simpl. destruct (nu c0). simpl. auto with bool. discriminate.
Qed.
*)
(*Lemma nu_Empt : forall (s : trace)(c : regex), nu (s \\ (Empt _;_ c)) = false.
Proof.
induction s;intros. now simpl. simpl. auto.
Qed.

Hint Rewrite nu_Empt.

Lemma nu_Eps : forall (s : trace)(c : regex), nu (s \\ (Eps _;_ c)) = nu (s \\ c).
Proof.
induction s;intros;simpl;auto. 
by rewrite derive_distr_plus /= nu_Empt //=.
Qed.*)

(*Lemma deriveP3
     : forall (c : regex) (e : A) (s : trace),
       Match (e :: s) c <-> Match s (\big[Plus/Empt]_(i <- (pd e c)) i).
Proof. intros. rewrite deriveP2 /pd_sum Match_big_undup //.
Qed.*)




(*Lemma seq_Eps : forall c, equiv (Eps _;_ c) c.
Proof.
move=> c s;split;intros. inversion H. inversion H3; subst. now simpl. by  apply/MSeq2;eauto.
Qed. 

Lemma seq_Empt : forall c, equiv (Empt _;_ c) Empt.
Proof.
move=> c s;split;intros. inversion H. inversion H3. inversion H.
Qed.

Hint Resolve seq_Eps seq_Empt.*)
(*Fixpoint derive2 s l := 
match s with 
|nil => l 
| a::s' =>derive2 s' (flatten (map (pd a) l))
end.

Lemma derive_nil : forall s, derive2 s nil = nil.
Proof. elim;ssa.
Qed.
Lemma trace_derive_cat : forall s l0 l1, derive2 s (l0 ++ l1) = (derive2 s l0) ++ (derive2 s l1).
Proof.
elim;ssa=>//=.  
elim: l0 l1 H;ssa. rewrite derive_nil /=. done.
rewrite !H0. rewrite H. rewrite catA. done. done.
Qed.*)
