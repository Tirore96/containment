From HB Require Import structures.
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving. 
Require Import Program. 
(*From Equations Require Import Equations.*)
Require Export Containment.regex.
From Containment Require Import tactics utils.


Set Implicit Arguments.
Set Maximal Implicit Insertion.

Let inE := utils.inE.


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

Section Enum.
Variable A : finType.
Implicit Type (r : @regex A).
Implicit Type (pp : @pder A * @pder A).
Fixpoint pi r := 
match r with 
| Eps => nil
| Empt => nil 
| Event _ => Eps::nil
| Plus r0 r1 =>  (pi r0) ++ (pi r1) 
| Seq r0 r1 => (map (fun x => x _;_ r1)(pi r0)) ++ (pi r1) 
| Star r0 => map (fun x => x _;_ Star r0 )(pi r0)
end.
Definition pi2 `(r: @regex A) := r::(pi r).





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
Definition pair_pd_l a pp := (pd_l a pp.1,pd_l a pp.2).

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
Hint Resolve undup_uniq.
Lemma measure_lt : forall V l, uniq_pair l -> l \notin V -> forall a,r_measure (l::V) (pair_pd_l a l) < r_measure V l.
Proof.
move=> V l Hun Hnotin a.
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

Definition vType := (seq (@pder A  * @pder A)).
Definition nType:= ((@pder A * @pder A)) %type.

Definition pType := (vType * nType)%type.
Definition myRel (p0 p1 : pType) := r_measure p0.1 p0.2 < r_measure p1.1 p1.2.
Lemma myRel_lt : forall V l, uniq_pair l -> l \notin V -> forall a, myRel (l::V,pair_pd_l a l) (V,l).
Proof.
intros. apply/measure_lt=>//.
Qed.

Lemma measure_rect
     : forall (P :  pType -> Type),
       (forall p,
           (forall p', myRel p' p  -> P p') -> P p) ->
       forall (p : pType) , P p.
Proof.
move=> P  Hsize u. 
have: Acc myRel u. clear Hsize. 
move Heq : (r_measure u.1 u.2)=>n. move: n Heq.
suff : forall n : nat, r_measure u.1 u.2 <= n -> Acc (fun p' p : pType => myRel p' p) u.
intros. eauto.
move=>n. elim: n u.
intros. con. intros. rewrite /myRel in H0. lia.
intros. con. intros. apply/H. rewrite /myRel in H1. lia.
move=>Hacc.
move: u Hacc Hsize. apply: Acc_rect.
intros.  apply/Hsize. intros. apply/X. done.
auto.
Defined.

Inductive D_bisim : vType -> nType -> Prop := 
| Db_stop V p : p \in V  -> D_bisim V p
| Db_next V p : p \notin V -> uniq_pair p -> (forall (a : A), D_bisim (p::V) (pair_pd_l a p)) -> D_bisim V p.

Lemma D_bisim_proj : forall V p, D_bisim V p -> p \notin V ->  (forall (a : A), D_bisim (p::V) (pair_pd_l a p)). 
Proof.
intros. destruct H. rewrite H in H0. simpl in H0. discriminate.
apply H2.
Defined.

Fixpoint reachable (V : vType) (p : nType)(P : @pder A -> @pder A -> bool)  (H : D_bisim V p)  {struct H} : bool.
refine(
match dec (p \in V) with 
| in_left => true (*avoid evaluating recursion if condition is true*)
| in_right => (P p.1 p.2) && (all (fun a => @reachable (p::V) (pair_pd_l a p) P _) (index_enum A))
end
).
move: (D_bisim_proj H). move=>HH. apply HH. rewrite e. done.
Defined.


Lemma D_bisim_make : forall (p : pType), uniq_pair p.2 -> D_bisim p.1 p.2.
Proof.
apply:measure_rect. 
intros. destruct (p.2 \in p.1) eqn:Heqn. con. done.
apply:Db_next. rewrite Heqn. done. done.
intros. 
move: (H (p.2::p.1,pair_pd_l a p.2)). ssa. apply/H1.
apply/myRel_lt. done. rewrite Heqn. done. 
rewrite /uniq_pair /pd_l. ssa; rewrite /pd_l; ssa.
Qed.

Lemma D_bisim_start : forall (l0 l1 : @pder A), D_bisim nil (undup l0,undup l1).
Proof.
intros. move: (D_bisim_make ((nil, (undup l0,undup l1)))). ssa.
apply/D_bisim_make0. rewrite /uniq_pair;ssa.
Qed.
Definition reachable_wrap (l0 l1 : @pder A) P := @reachable nil (undup l0,undup l1) P (D_bisim_start l0 l1).
End Enum.



