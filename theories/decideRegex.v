From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Program.
From Paco Require Import paco.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Ltac con := constructor. 
Ltac econ := econstructor.
Ltac case_if := match goal with 
    | [ |- context[if ?X then _ else _ ]] => have : X by subst
    | [ |- context[if ?X then _ else _ ]] => have : X = false by subst 

    | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).
Ltac rifliad := (repeat case_if); try done.

Lemma neg_sym : forall (A : eqType) (a b : A), (a != b) = (b != a).
Proof.
intros. destruct (eqVneq a b).  done. done. 
Qed.

Ltac split_ando :=
  intros;
   repeat
    match goal with
    | H:is_true (_ && _) |- _ => destruct (andP H); clear H
    | H:_ && _ = true |- _ => destruct (andP H); clear H
    | H:_ /\ _ |- _ => destruct H
    | |- _ /\ _ => con
    | |- is_true (_ && _) => apply /andP ; con
    | |- is_true (_ || _) => apply /orP
    | H : ex _ |- _ => destruct H
    end; auto.

Notation eq_iff := Bool.eq_iff_eq_true.
Ltac ssa := rewrite ?inE;simpl in *; split_ando;try done.

Ltac de i := destruct i;ssa.
Ltac inv H := inversion H;subst;try done. 
Ltac norm_eqs := repeat 
(match goal with 
                   | [ H : is_true (_ == _) |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = true |- _ ] => move : H => /eqP=>H
                   | [ H : (_ == _) = false |- _ ] => move : H => /negbT=>H

                  end);subst;repeat (match goal with 
                   | [ H : is_true (?a != ?a_) |- _ ] => rewrite eqxx in H;done 

                  end).

Let inE := (inE, eqxx,negb_or,negb_and).

Lemma my_in_cons : forall (A :eqType) (a : A) l, a \in (a::l).
Proof. intros. rewrite !inE. done. Qed.

Lemma my_in_cons2 : forall (A :eqType) (a a0 : A) l, a \in l -> a \in (a0::l).
Proof. intros. rewrite !inE H. lia. Qed.


Hint Resolve my_in_cons my_in_cons2.

Lemma negb_involutive : forall b, ~~ ~~ b = b. case;done. Qed.

Fixpoint compose {A B C : Type} (aa : seq A) (bb : seq B) (r : A -> B -> C) :=
match aa with 
| nil => nil
| a::aa' => (map (r a) bb) ++ (compose aa' bb r)
end.

Lemma mem_compose :
  forall (A B C : eqType) (aa : seq A) (bb : seq B) (a : A) (b : B) (r : A -> B -> C),
 a \in aa -> b \in bb -> r a b \in compose aa bb r.
Proof. move => A B C. elim;intros. done. 
simpl. rewrite mem_cat. rewrite !inE in H0. destruct (orP H0). rewrite (eqP H2).
apply/orP. left. apply/map_f. done. apply/orP. right. apply/H. done. done. 
Qed.

Lemma mem_compose2 : forall (A B : eqType) aa bb (a : A) (b : B),   pair a b \in
   compose aa bb pair ->  a \in aa /\ b \in bb.
Proof. move => A B. elim;intros. done. move : H0=>/=. rewrite mem_cat. move/orP. 
case. move/mapP=>[] //=. intros. inversion q. subst. rewrite inE //= eqxx. lia. 
move/H. case. rewrite inE. move=>->. ssa. 
Qed.

Arguments rem {_}.
Fixpoint rep_rem {A : eqType} (xs l : seq A) :=
match xs with 
| nil => l 
| x::xs' => rem x (rep_rem xs' l)
end. 

Lemma mem_rem : forall (A : eqType) l' (a a' : A), a != a' -> a \in l' ->  
a \in rem a' l'.  
Proof. 
move => A. elim. done. 
intros. simpl. case_if. move : H2. move/eqP=>HH. subst. rewrite inE in H1. 
move : H1. move : (negbTE H0)=>-> //=. move : H1. 
rewrite !inE. move/orP. case. move=>-> //=. move/H=>->. lia. done. 
Qed.

Lemma mem_rem2 : forall (A : eqType) l' (a a' : A), a != a' -> a \in rem a' l'  ->
 a \in l'.  
Proof. 
move => A. elim. done. intros. simpl in H1. move : H1. case_if. 
rewrite inE. move=>->. lia. rewrite inE. move/orP=>[]. move/eqP=>->. done. 
move/H. rewrite inE. move=>->. lia. lia. 
Qed.

Lemma mem_rep_rem : forall (A : eqType) l l' (a : A), a \notin l -> a \in l' ->  
a \in rep_rem l l'.  
Proof. 
move => A. elim. done.
intros. simpl. rewrite inE negb_or in H0. ssa. apply/mem_rem. done. auto. 
Qed.

Lemma mem_rep_rem2 : forall (A : eqType) l l' (a : A), a \in rep_rem l l' -> 
a \notin l -> a \in l'.  
Proof. 
move => A. elim. done. intros. simpl. rewrite inE negb_or in H1. ssa.
apply mem_rem2 in H0.  auto. lia. 
Qed.

Lemma mem_rep_iff : forall (A : eqType) l l' (a : A),  a \notin l  -> a \in l'  <-> 
a \in rep_rem l l'.
Proof. 
move => A. intros. split;intros. apply/mem_rep_rem;auto. 
apply/mem_rep_rem2;eauto. 
Qed.

Lemma rep_rem2 : forall (A : eqType) (l l0 l1 : seq A) a, a \notin l -> 
(forall x, x \in l0 -> x \in l1) ->a \in rep_rem l l0  -> a \in rep_rem l l1.
Proof. 
move => A. elim. 
simpl. intros. auto.
simpl.  ssa. rewrite inE negb_or in H0.  ssa. 
apply/mem_rem. done. apply/H.  done. eauto. apply/mem_rem2. eauto. done. 
Qed.

Lemma rep_rem_uniq: forall (A : eqType) (l l' : seq A), uniq l' -> 
uniq (rep_rem l l').
Proof. 
move => A.
elim.  done. 
intros. simpl. rewrite rem_uniq. done. auto. 
Qed.

Lemma size_strict_sub : forall (A : eqType) (l l' : seq A) a, uniq l  -> 
(forall x, x \in l -> x \in l') -> a \notin l -> a \in l' -> size l < size l'. 
Proof. 
intros. 
have : size (a::l) <= size l'. 
apply/uniq_leq_size. ssa. move => x0 x1. 
rewrite inE in x1. destruct (orP x1). rewrite (eqP H3). done. auto. done. 
Qed.

Lemma rem_uniq2 : forall (A: eqType) (l'  : seq A) a x, uniq l' -> 
x <> a -> x \notin l' ->   x \notin rem a l'.
Proof.
move => A. elim. done. intros. ssa. case_if. 
rewrite inE negb_or in H2. ssa. 
rewrite inE negb_or. ssa. rewrite inE negb_or in H2. ssa. 
apply/H. ssa. done. rewrite inE negb_or in H2. ssa. 
Qed.

Lemma rep_rem_uniq2 : forall (A: eqType) (l l' : seq A) x, uniq l' ->  x \in l -> 
x \notin rep_rem l l'.
Proof. 
move => A. elim. done. intros. rewrite inE in H1. destruct (eqVneq x a).  subst. 
simpl. rewrite mem_rem_uniqF. done. apply/rep_rem_uniq. done.
simpl. simpl in H1. apply/rem_uniq2. apply/rep_rem_uniq. done. apply/eqP. done.
auto.  
Qed.

Notation In := List.In.

Lemma inP : forall {A : eqType} l (g : A) , reflect (In g l) (g \in l).
Proof.
move => A. elim. rewrite /=. intros. rewrite in_nil. constructor. done.
- move => a l H g. rewrite /=. apply Bool.iff_reflect. split. case.
move=>->. by rewrite in_cons eqxx. rewrite in_cons. move/H=>->.
by rewrite orbC. 
rewrite inE. move/orP =>[].  move/eqP=>->. auto. move/H. auto.
Qed.

Definition uniq_pair {A : eqType} (pp  : (seq A) * (seq A)):= 
uniq pp.1 && uniq pp.2.

Definition is_sub {A: eqType} (l0 l1 : seq A) := forall x, x \in l0 -> x \in l1.

Definition is_sub_bool {A : eqType} (l0 l1 : seq A) := all (fun x => x \in l1) l0. 
Lemma is_subP: forall (A : eqType) (l0 l1 : seq A), is_sub l0 l1 <-> is_sub_bool l0 l1.
Proof.
intros. split. rewrite /is_sub. intros. apply/allP. intro. eauto.
move/allP.  eauto.
Qed.

Fixpoint enum (A : Type) (n : nat) (R : seq A) := 
match n with 
| 0 => nil::nil 
| n'.+1 => (compose R (enum n' R) cons)++(enum n' R)
end.

Lemma in_enum_nil : forall (A : eqType) n (R : seq A), nil \in enum n R. 
Proof. move=> A'. elim;ssa. rewrite mem_cat H. lia. Qed.

Lemma in_enum : forall (A : eqType) n R (l : seq A), size l <= n ->
 (forall x, x \in l -> x \in R) -> l \in enum n R. 
Proof.
move=> A'. elim;ssa. destruct l;ssa.
destruct l. rewrite mem_cat in_enum_nil. lia.
rewrite mem_cat. apply/orP. left. apply/mem_compose. eauto. eauto.
Qed.

Lemma uniq_size : forall (A : eqType) (l : seq A) R, uniq l -> 
(forall x, x \in l -> x \in R) -> size l <= size R.
Proof.
move=> A'. elim;ssa. have : forall x, x \in l -> x \in R. eauto.
move=> Hin. move: (H _ H3 Hin). move=>Hsize.
move: (H1 a). rewrite !inE /=. move/(_ is_true_true)=>Hr.
apply:size_strict_sub. done. done. eauto. done.
Qed.

Lemma in_enum_uniq : forall (A : eqType) R (l : seq A), uniq l -> 
(forall x, x \in l -> x \in R) -> l \in enum (size R) R. 
Proof. intros. apply:in_enum.  apply:uniq_size. done. done. done. Qed.

Lemma mem_compose_cons : forall (B : eqType) (aa : seq B) bb l,  
 l \in compose aa bb cons -> exists a b, l = cons a b /\  a \in aa /\ b \in bb.
Proof. 
move => B. elim;intros. done. move : H0=>/=. rewrite mem_cat. move/orP.
case. move/mapP=>[] //=. intros. inversion q. subst. econ. econ.  eauto.
move/H. case. ssa. subst. econ. econ. eauto.
Qed.

Lemma enum_inR : forall (A : eqType) n R (l : seq A) x, l \in enum n R -> 
x \in l -> x \in R. 
Proof.
move=> A'. elim;ssa. rewrite !inE in H. norm_eqs. done.
rewrite mem_cat in H0. de (orP H0). apply mem_compose_cons in H2. ssa. subst. 
rewrite !inE in H1. de (orP H1). norm_eqs. done. eauto. eauto.
Qed.

Section Regex.
Variable (A : finType).
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


Lemma MSeq2: forall s0 s1 c0 c1 s, Match s0 c0 -> Match s1 c1 -> s = s0 ++ s1  -> 
Match s (c0 _;_ c1).
Proof.
move => s0 s1 c0 c1 s HM0 HM1 Heq;subst. eauto.
Qed.

Lemma MStar2 : forall s0 s1 c s, Match s0 c -> Match s1 (Star c) -> s = s0 ++ s1  -> 
Match s (Star c).
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

Lemma derive_distr_plus : forall (s : trace)(c0 c1 : regex), 
s \\ (c0 _+_ c1) = s \\ c0 _+_ s \\ c1.
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

Lemma Match_nil_seq: forall c0 c1, Match nil (Seq c0 c1) -> 
Match nil c0 /\ Match nil c1.
Proof.
move=> c0 c1 HM. inversion HM;subst. destruct s1;ssa. destruct s2;ssa.
Qed.

Lemma nuP : forall c, nu c <-> Match [::] c.
Proof.
move=> c. con;first by apply/Match_nil_nu=>//.
elim: c=>//=. move=> HM. inv HM. move=> s HM. inv HM.
move=> r IH r0 HM HM2. apply/orP. inv HM2;eauto.
move=> r IH r0 IH2 HM. apply/andP. move/Match_nil_seq: HM=>[]. eauto.
Qed.

Lemma Match_matchb : forall (c : regex)(e : A)(s : trace), Match s (e \ c)-> 
Match (e::s) c.
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

Theorem matchbP: forall (c : regex)(s : trace), Match s c <-> matchb s c. 
Proof.
move=> c s. rewrite /matchb.
split;first by apply/Match_i_matchb=>//.
elim: s c=>//;first by move=> c /Match_nil_nu=>//.
move=> a l IH c /=. move/IH/Match_matchb=>//.
Qed.

Lemma deriveP: forall (c : regex)(e : A)(s : trace), Match (e::s) c <-> Match s (e \ c).
Proof.
by move=> c e s; rewrite !matchbP.
Qed.

Fixpoint pd a r := 
match r with 
| Eps => nil 
| Empt => nil 
| Event a' => if a == a' then Eps::nil else nil
| Plus r0 r1 => (pd a r0) ++ (pd a r1)
| Seq r0 r1 => if nu r0 then (map (fun x => Seq x r1) (pd a r0)) ++ (pd a r1) 
              else (map (fun x => Seq x r1) (pd a r0))
| Star r0 => map (fun x => x _;_ Star r0) (pd a r0)
end.

Definition pd_l a l := undup (flatten (map (pd a) l)).
Definition pd_sum a r := \big[Plus/Empt]_(r <- (pd a r)) r.
Definition pder := seq regex.

Lemma Match_big_undup : forall l s, Match s (\big[Plus/Empt]_(i <- undup l) i)  <-> 
 Match s ((\big[Plus/Empt]_(i <- l) i)).
Proof.
elim;ssa. case_if. rewrite !big_cons. split.
move/H. eauto. intros. apply/H. inv H1;eauto. 
clear H1 H. elim: l a H0 H4;ssa.  rewrite !inE in H0. de (orP H0). norm_eqs. 
rewrite big_cons. eauto. rewrite big_cons. eauto. 
rewrite !big_cons. split. intros. inv H1;eauto. constructor 5. apply/H. done.
intros. inv H1;eauto. constructor 5. apply/H. done.
Qed.

Lemma Match_big_cat : forall l  l' s, Match s (\big[Plus/Empt]_(i <- l ++ l') i)  <->  
Match s ((\big[Plus/Empt]_(i <- l) i) _+_  (\big[Plus/Empt]_(i <- l') i)).
Proof.
split. elim: l l' s. ssa. 
move=> a l IH l' s.  rewrite /= !big_cons. intros. inv H. eauto.
apply IH in H2. inv H2. eauto. eauto.
elim: l l' s. ssa. rewrite big_nil in H.  inv H. inv H2.
move=> a l IH l' s.  rewrite /= !big_cons. intros. inv H. inv H2. eauto. 
constructor 5. apply:IH. eauto. eauto.
Qed.

Lemma Match_factor_r : forall l s r (F : regex -> regex), 
Match s (\big[Plus/Empt]_(i <- l) (F i _;_ r)) -> 
Match s (\big[Plus/Empt]_(i <- l) (F i) _;_ r). 
Proof.
elim;ssa. rewrite big_nil in H. inv H.
move: H0. rewrite !big_cons. intros. inv H0. inv H3. eauto. 
apply H in H3. inv H3. eauto.
Qed.

Lemma Match_factor_r2 : forall l s r (F : regex -> regex),  
Match s (\big[Plus/Empt]_(i <- l) (F i) _;_ r) -> 
Match s (\big[Plus/Empt]_(i <- l) (F i _;_ r)). 
Proof.
elim;ssa. rewrite big_nil in H. inv H. inv H3.
move: H0. rewrite !big_cons. intros. inv H0. inv H4. eauto. eauto.
Qed.

Lemma map_big_plus : forall l (f : regex -> regex), 
\big[Plus/Empt]_(a <- map f l) a = \big[Plus/Empt]_(a <- l) (f a).
Proof.
elim;ssa. rewrite !big_nil. done. rewrite !big_cons. f_equal. done.
Qed.

Lemma has_nu_Match : forall l, Match [::] (\big[Plus/Empt]_(i <- l) i) ->  has nu l.
Proof.
elim;ssa. rewrite big_nil in H. inv H. rewrite !big_cons in H0. inv H0. 
left. rewrite matchbP /matchb // in H3. eauto.
Qed.

Lemma Match_has_nu : forall l, has nu l ->  Match [::] (\big[Plus/Empt]_(i <- l) i).
Proof.
elim;ssa. de (orP H0). rewrite !big_cons /=. con. apply:Match_nil_nu. done.
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
rewrite eq_sym H big_nil //=. inv H1. apply H in H4.
move: H4. move: (pd e r0)=> l. intros. apply/Match_big_cat. eauto.
apply H0 in H4. apply/Match_big_cat. eauto. destruct (nu _) eqn:Heqn.  
apply/Match_big_cat.  inv H1.  inv H4. con. apply H in H6. 
rewrite map_big_plus. apply Match_factor_r2. eauto. eauto. 
inv H1.  apply H in H5. rewrite map_big_plus. apply Match_factor_r2. eauto.
inv H0. rewrite map_big_plus. apply Match_factor_r2. eauto. rewrite /pd_sum.
elim: r s e;ssa.  rewrite big_nil // in H. rewrite big_nil // in H.
move: H. case_if. norm_eqs. rewrite eqxx. rewrite !big_cons big_nil. intros. 
inv H. inv H2. 
rewrite eq_sym H big_nil //=. apply Match_big_cat in H1. inv H1. eauto. eauto.
destruct (nu _) eqn:Heqn.  apply Match_big_cat in H1. inv H1. 
rewrite map_big_plus in H4. apply Match_factor_r in H4. inv H4. eauto. eauto.
rewrite map_big_plus in H1. apply Match_factor_r in H1. inv H1. eauto. 
rewrite map_big_plus in H0. apply Match_factor_r in H0. inv H0. eauto.
Qed.

Lemma deriveP2
     : forall (c : regex) (e : A) (s : trace),
       Match (e :: s) c <-> Match s (pd_sum e  c).
Proof. intros. rewrite -der_eq. apply/deriveP. Qed.

Lemma pd_plus : forall l e, undup (pd e (\big[Plus/Empt]_(i <- l) i)) = pd_l e l.
Proof.
rewrite /pd_l. elim;ssa. rewrite big_nil. done.
rewrite big_cons /=. rewrite !undup_cat.  f_equal;try done. 
apply/eq_in_filter. intro. ssa.   clear H0.
move: x. clear H.  elim: l. ssa. rewrite big_nil. done. 
intros. rewrite !big_cons /=. rewrite !mem_cat !negb_or. f_equal. eauto.
Qed.

Lemma big_derive : forall (l : pder) e, e \ \big[Plus/Empt]_(i <- l) i = 
                                     \big[Plus/Empt]_(i <- map (derive e)l) i.
Proof.
elim;ssa. rewrite !big_nil //. rewrite !big_cons //=. f_equal. done.
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
Definition pi2 (r: @regex) := r::(pi r).

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
  move: (H _ _ _ H3 H2). ssa. move: (H0 _ _ _ H3 H2). ssa. 
- rewrite !mem_cat in H1 *. 
  destruct (orP H1). destruct (mapP H3). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H2. destruct (orP H2).
  destruct (mapP H5). subst. move: (H _ _ _ H4 H6). ssa. 
  con. apply/map_f. done. eauto. destruct (mapP H2). subst. 
  move: (H _ _ _ H4 H5). ssa. left. apply/map_f. eauto. move: (H0 _ _ _ H3 H2).
  ssa.  
- destruct (mapP H0). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H1. destruct (orP H1). 
  destruct (mapP H3). subst. move: (H _ _ _ H2 H4). ssa. apply/map_f. eauto.
  destruct (mapP H3). subst. apply:map_f. eauto.
  destruct (mapP H1). subst. ssa. move: (H _ _ _ H2 H3). ssa. apply/map_f.
  eauto.
Qed.

Lemma in_pd_pi : forall r0 r1 r2 a, r1 \in pd a r0 -> r2 \in pi r1 -> r2 \in pi r0.
Proof.
elim;ssa.
- move:H. rifliad. norm_eqs. rewrite !inE. intros. norm_eqs. ssa.
- rewrite !mem_cat in H1 *.  destruct (orP H1).  
  move: (H _ _ _ H3 H2). ssa. move: (H0 _ _ _ H3 H2). ssa. 
- rewrite !mem_cat in H1 *. 
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
  apply/map_f. eauto. destruct (mapP H3). subst. apply:map_f. eauto.
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

Lemma in_pd_enum_aux : forall (l l' : seq regex) a, l' \in  enum_pi2 (pd_l a l) ->  
l' \in enum_pi l.
Proof.
intros. apply:in_enum_uniq. de (mapP H). subst. apply:undup_uniq.
intros. ssa. rewrite /enum_pi2 in H. de (mapP H). subst.
rewrite /pi_l. rewrite mem_undup. 
apply/flattenP. simpl. rewrite mem_undup in H0.
move: (@enum_inR _ _ _ _ _ H1 H0).
move=>Hin. rewrite /pi_l in Hin. rewrite mem_undup in Hin.
de (flattenP Hin). de (mapP H2). subst. 
rewrite /pd_l in H4. rewrite mem_undup in H4. de (flattenP H4). de (mapP H5).
subst. econ. apply/map_f. 2: { apply:in_pd_pi2.  apply:H6.  done. } done.
Qed.

Lemma in_pd_enum : forall (l l' : seq regex) a, l' \in  enum_pi2 (pd_l a l) ->  
l' \in enum_pi2 l.
Proof.
intros. move: (in_pd_enum_aux _ _ _ H). intros. de (mapP H). subst.
apply/mapP. econ.  eauto. symmetry. rewrite undup_id //. apply/undup_uniq.
Qed.

Lemma enum_pi_self : forall l, uniq l ->  l \in enum_pi l.
Proof.
intros. apply:in_enum_uniq. done. intros. rewrite /pi_l. rewrite mem_undup.
apply/flattenP. simpl. econ. apply/map_f. eauto. rewrite !inE //.
Qed.

Lemma enum_pi2_self : forall l, uniq l ->  l \in enum_pi2 l.
Proof.
intros. apply enum_pi_self in H as H'. 
rewrite /enum_pi2. apply/mapP. econ. eauto. rewrite undup_id //.
Qed.
Hint Resolve enum_pi2_self.

Definition pair_enum ee := compose (enum_pi2 ee.1) (enum_pi2 ee.2) pair. 
Definition pair_pd_l a pp := (pd_l a pp.1,pd_l a pp.2).

Lemma selfee : forall pp, uniq_pair pp ->  pp \in pair_enum pp. 
Proof. case. intros. rewrite /uniq_pair in H. ssa.
rewrite /pair_enum /=. apply/mem_compose;eauto.
Qed.
Hint Resolve selfee.

Lemma in_pd_pair_enum : forall l l' a, l' \in  pair_enum (pair_pd_l a l) ->  
l' \in pair_enum l.
Proof.
intros. rewrite /pair_enum in H.  rewrite /pair_enum. destruct l'. 
apply mem_compose2 in H. destruct H. ssa. destruct l. ssa. 
apply/mem_compose. apply:in_pd_enum. apply:H. apply:in_pd_enum. apply:H0.
Qed.

Definition r_measure ( visited : seq (pder * pder)) (l : pder * pder) := 
size (rep_rem visited (undup (pair_enum l))). 

Hint Resolve undup_uniq.
Lemma measure_lt : forall V l, uniq_pair l -> l \notin V -> 
forall a,r_measure (l::V) (pair_pd_l a l) < r_measure V l.
Proof.
move=> V l Hun Hnotin a. intros. rewrite /r_measure. 
simpl. destruct (l \in (pair_enum (pair_pd_l a l))) eqn:Heqn.
- apply/size_strict_sub. apply/rem_uniq/rep_rem_uniq/undup_uniq. 
 * intros. destruct (eqVneq x l).
  **  subst. rewrite -mem_rep_iff.  rewrite mem_undup. eauto. 
      apply/pair_enum_self. done.*) done. 
  ** apply mem_rem2 in H;eauto. 
     have : x \notin V. apply/negP=>HH. eapply rep_rem_uniq2 in HH.
     2: { instantiate (1:= undup (pair_enum (pair_pd_l a l))).  done. }
     rewrite H //= in HH. move => Heqn2.
     move : H. rewrite -!mem_rep_iff;eauto. 
     rewrite  !mem_undup. intros. apply/in_pd_pair_enum. eauto.
 * instantiate (1 := l).  apply/negP=>HH. rewrite mem_rem_uniqF in HH. done. 
   apply/rep_rem_uniq/undup_uniq. 
 * rewrite -mem_rep_iff.  rewrite mem_undup. eauto.  done.
- have :  l \notin rep_rem V (undup (pair_enum (pair_pd_l a l))). 
  apply/negP=>HH. move : Heqn. move/negP=>H2. apply/H2. 
  apply/mem_rep_iff.  apply:Hnotin. apply/rep_rem2. done.
  2 :  eauto.  intros. rewrite mem_undup in H. done. move => HH'. 
  rewrite rem_id //=. apply/size_strict_sub;eauto.   
  * apply/rep_rem_uniq. apply/undup_uniq. (*uniquenes not interesting*)
  * intros. have : x \notin V. apply/negP=>HH. eapply rep_rem_uniq2 in HH. 
    2: {  instantiate (1:= undup (pair_enum (pair_pd_l a l))).  done. }
    rewrite H //= in HH. move => Heqn2. (*x \notin V*)
    move : H. rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. 
    apply:in_pd_pair_enum. eauto. done. done.
  * rewrite -mem_rep_iff. rewrite mem_undup. eauto. done.
Qed.

Definition vType := (seq (@pder   * @pder )).
Definition nType:= ((@pder  * @pder)) %type.

Definition pType := (vType * nType)%type.
Definition myRel (p0 p1 : pType) := r_measure p0.1 p0.2 < r_measure p1.1 p1.2.
Lemma myRel_lt : forall V l, uniq_pair l -> l \notin V -> 
forall a, myRel (l::V,pair_pd_l a l) (V,l).
Proof. intros. apply/measure_lt=>//. Qed.

Lemma measure_rect
     : forall (P :  pType -> Type), (forall p,  (forall p', myRel p' p  -> P p') -> P p) -> 
forall (p : pType) , P p.
Proof.
move=> P  Hsize u. 
have: Acc myRel u. clear Hsize. 
move Heq : (r_measure u.1 u.2)=>n. move: n Heq.
suff : forall n : nat, r_measure u.1 u.2 <= n -> Acc (fun p' p : pType => myRel p' p) u.
intros. eauto. move=>n. elim: n u. intros. con. intros. rewrite /myRel in H0. 
lia. intros. con. intros. apply/H. rewrite /myRel in H1. lia. move=>Hacc.
move: u Hacc Hsize. apply: Acc_rect. intros.  apply/Hsize. intros. apply/X. 
done. auto.
Defined.

Inductive D_bisim : vType -> nType -> Prop := 
| Db_stop V p : p \in V  -> D_bisim V p
| Db_next V p : p \notin V -> uniq_pair p -> (forall (a : A), D_bisim (p::V)
                                             (pair_pd_l a p)) -> D_bisim V p.

Lemma D_bisim_proj : forall V p, D_bisim V p -> p \notin V ->  
                            (forall (a : A), D_bisim (p::V) (pair_pd_l a p)). 
Proof.
intros. destruct H. rewrite H in H0. simpl in H0. discriminate. apply H2.
Defined.

Fixpoint reachable (V : vType) (p : nType)(P : @pder -> @pder -> bool)  
         (H : D_bisim V p)  {struct H} : bool.
refine(
match dec (p \in V) with 
| in_left => true (*avoid evaluating recursion if condition is true*)
| in_right => (P p.1 p.2) && 
              (all (fun a => @reachable (p::V) (pair_pd_l a p) P _) (index_enum A))
end
).
move: (D_bisim_proj H). move=>HH. apply HH. rewrite e. done. Defined.

Lemma D_bisim_make : forall (p : pType), uniq_pair p.2 -> D_bisim p.1 p.2.
Proof.
apply:measure_rect. intros. destruct (p.2 \in p.1) eqn:Heqn. con. done.
apply:Db_next. rewrite Heqn. done. done. intros. 
move: (H (p.2::p.1,pair_pd_l a p.2)). ssa. apply/H1.
apply/myRel_lt. done. rewrite Heqn. done. 
rewrite /uniq_pair /pd_l. ssa; rewrite /pd_l; ssa.
Qed.

Lemma D_bisim_start : forall (l0 l1 : @pder), D_bisim nil (undup l0,undup l1).
Proof.
intros. move: (D_bisim_make ((nil, (undup l0,undup l1)))). ssa.
apply/D_bisim_make0. rewrite /uniq_pair;ssa.
Qed.
Definition reachable_wrap (l0 l1 : @pder ) P := 
@reachable nil (undup l0,undup l1) P (D_bisim_start l0 l1).
Definition equiv_o := (fun ( l0 l1 : @pder ) => has nu l0 == has nu l1).

Inductive exten_gen bisim : pder -> pder-> Prop :=
 contains_con2 l0 l1 (H0: forall e, bisim (pd_l e l0) (pd_l e l1) : Prop ) 
               (H1: equiv_o l0 l1) : exten_gen bisim l0 l1.

Definition Extensional l0 l1 := paco2 (exten_gen) bot2 l0 l1.
Hint Unfold  Extensional : core.

Lemma exten_gen_mon : monotone2 (exten_gen ). 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve exten_gen_mon : paco.

Definition equiv_l s (l0 l1 : @pder) := Match s (\big[Plus/Empt]_(a <- l0) a) <->
                                          Match s (\big[Plus/Empt]_(a <- l1) a).
Lemma Pb_P_iff2 : forall l l', equiv_o  l l' <->  equiv_l [::] l l'.
Proof.
intros. rewrite /equiv_o /equiv_l. rewrite -!Match_has_nu_iff. split. 
move/eqP. move=>->//=. move/eq_iff. move=>->//=.
Qed.

Lemma P_undup2 : forall l0 l1, (forall s, equiv_l s l0 l1  <-> 
equiv_l s (undup l0) (undup l1)).
Proof.
intros. rewrite /equiv_l. rewrite !Match_big_undup //.
Qed.

Lemma P_derive2 : forall a l0 l1, forall s, equiv_l s  (pd_l a l0) (pd_l a l1) <->
 equiv_l (a :: s) l0 l1.  
Proof.
intros. rewrite /equiv_l. rewrite -!pd_plus. rewrite !Match_big_undup.
rewrite !deriveP2. done.
Qed.

Theorem equiv_rInd : forall l l', Extensional l l' -> forall s, equiv_l s l l'.  
Proof.
move=> l0 l1 HC s. elim: s l0 l1  HC.
- move=> c0 c1. ssa. punfold HC. case: HC. move=> ce c3 HC HC'.
  rewrite /equiv_l -!Match_has_nu_iff. rewrite /equiv_o in HC'. 
  rewrite (eqP HC') //.
- move=> a l IH c0 c1. move=>HC.  punfold HC. case: HC. intros.
  case: (H0 a)=>//. intros. rewrite -P_derive2. apply: IH. done.
Qed.

Theorem Bisim_co_ind2 : forall l l', (forall s, equiv_l s l l') -> Extensional l l'.
Proof.
pcofix CIH. move=> l l'. pfold. con.  intros. right. apply:CIH. intros.
apply P_derive2. apply H0. apply/Pb_P_iff2. done.
Qed.

Lemma Extensional_equiv : forall l l', Extensional l l' <->  forall s, equiv_l s l l'. 
Proof.
intros. split. apply/equiv_rInd. apply:Bisim_co_ind2.
Qed.

Fixpoint bisim_complete_aux p l_v (H : D_bisim l_v p) {struct H} :  
Extensional p.1 p.2 ->  reachable equiv_o H.  
refine( match H with 
        | Db_stop x y z => _ 
        | _ => _ 
        end).
simpl in x,y,z. intros. 
have:  exten_gen (upaco2 (exten_gen) bot2) y.1 y.2. clear bisim_complete_aux. 
punfold H0. clear H0. move=> He.  move: He z. case. intros. simpl. 
destruct (Utils.dec _). done. exfalso. rewrite z in e. done. simpl in p0. 
intros. have:  exten_gen (upaco2 (exten_gen) bot2) p1.1 p1.2. punfold H0.
clear H0=>H0. destruct p1. simpl in *. destruct (Utils.dec _). done.
move: H0 i i0 d. clear e. case. intros. ssa. 
apply/allP. intro. intros. apply (bisim_complete_aux _ _ (d x)). simpl.
clear bisim_complete_aux. simpl. case: (H0 x). ssa. done.
Qed.

Lemma bisim_complete : forall l0 l1, Extensional l0 l1 ->  
reachable_wrap l0 l1 equiv_o.
Proof. intros. apply:bisim_complete_aux. simpl. apply/Extensional_equiv. 
intro. apply -> P_undup2. move: s. apply/Extensional_equiv=>//.
Qed.

Fixpoint bisim_sound_aux p l_v (H : D_bisim l_v p) 
         (R : @pder  -> @pder  -> Prop) {struct H} : 
(forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   
reachable equiv_o H -> upaco2 exten_gen R p.1 p.2. 
refine( match H with 
        | Db_stop x y z => _ 
        | _ => _ 
        end).
- ssa. right.  apply/H0. destruct y. ssa. 
- simpl. intros. left. destruct (Utils.dec _). rewrite e in i. done.
  destruct (andP H1). pcofix CIH. pfold. con. intros. 
  eapply (bisim_sound_aux (pd_l e0 p1.1,pd_l e0 p1.2)). simpl. 
  2: { apply (allP H3). done. } 
  intros. rewrite !inE in H4. destruct (orP H4).   norm_eqs. ssa.  eauto. done.
Qed.

Lemma bisim_sound : forall e0 e1, reachable_wrap e0 e1 equiv_o -> Extensional e0 e1.  
Proof. move => e0 e1 H. rewrite /reachable_wrap in H. 
apply:Bisim_co_ind2=>s. apply/P_undup2. move: s. apply/Extensional_equiv.
apply (@bisim_sound_aux _ _ _ bot2) in H. ssa. inv H. ssa.
Qed.

Lemma P_decidable_aux : forall l0 l1, reachable_wrap l0 l1 equiv_o <-> 
                                   (forall s, equiv_l s l0 l1).
Proof. 
intros. split. move/bisim_sound. move/Extensional_equiv.
move=> H s. eauto. intros. apply/bisim_complete. apply/Bisim_co_ind2. done.
Qed.

Lemma plus_empt : forall r s, Match s r <-> Match s (r _+_ Empt).
Proof. intros. split. eauto. intros. inv H. inv H2. Qed.

Definition regex_decide (r0 r1 : regex) := reachable_wrap ([::r0]) [::r1] equiv_o.
Lemma P_decidable : forall r0 r1, regex_decide r0 r1 <-> 
                               (forall s, Match s r0 <-> Match s r1).  
Proof. intros.  rewrite P_decidable_aux.  
rewrite /equiv_l. rewrite !big_cons !big_nil. 
split.  intros. split. intros. apply/plus_empt. apply/H. con. done.
intros. apply/plus_empt. apply/H. con. done.
intros. split. intros. apply -> plus_empt. apply plus_empt in H0. apply/H. done.
intros. apply -> plus_empt. apply plus_empt in H0. apply/H. done.
Qed.
