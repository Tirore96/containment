



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
| rule_guard a r r' pf p : full_unf pf = guard p -> P r r' p -> (Event a) _;_ r <R= (Event a) _;_ r' ~> pf
 where "c1 <R= c2 ~> p" := (c_ineq c1 c2 p).
End Containment.
Hint Constructors c_ineq.
Lemma c_ineq_gen_mon: monotone3 c_ineq. 
Proof.
unfold monotone3.
intros. induction IN; eauto. 
Qed.
Hint Resolve c_ineq_gen_mon : paco.

Notation "c0 < ( R ) = c1 ~> p" := (c_ineq R c0 c1 p)(at level 63).
Definition INEQ c0 c1 p := paco3 c_ineq bot3 c0 c1 p.
Notation "c0 <C= c1 ~> p" := (INEQ c0 c1 p)(at level 63).



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


(*Uses two fixpoints*)
Lemma star_star_co_ineq : forall a,  (Star (Star (Event a))) <C= (Star (Event a)) ~> d6.
Proof.
move=> a.  pfold.

apply: rule_ctrans=>//. apply: rule_cstar=>//. apply: rule_wrapinv=>//.

apply/rule_ctrans=>//. apply/rule_drop=>//.
apply/rule_ctrans=>//. apply/rule_wrapinv=>//.
apply/rule_ctrans=>//. 2: { apply/rule_wrap=>//. }
apply/rule_cplus=>//. apply/rule_cid=>//.
apply/rule_ctrans=>//. apply/rule_assoc=>//.
(*apply/rule_guard=>//. left. pcofix CIH. pfold*)  
apply/rule_cseq=>//. apply/rule_cid=>//. (*Don't use rule_guard yet*) (*apply/rule_guard=>//. left=>//. pfold.*)

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
apply/rule_guard=>//. right. apply/CIH.

apply/rule_ctrans=>//. apply/rule_assoc=>//.
apply/rule_guard=>//. right.  apply/CIH2.
Qed.












Lemma star_star_ind_eq : forall c, Star c =⟨nil⟩= Star (Star c).
Proof. 
intros. (* (Star c, (Star (Star c))) in pgfp(bot2)(F)*) 
 (* (Star c, (Star (Star c))) in F(bot2 union R*) 
apply:c_trans. apply:derive_unfold. apply:c_trans.
2: { apply:c_sym. apply:derive_unfold. } 
apply:c_plus_ctx. done. 
move: (index_enum A) => l. 
elim: l. rewrite !big_nil. done. 
intros. rewrite !big_cons. apply:c_plus_ctx;last done.  (*bot2 union gfp(F)*)
clear H. simpl. 
apply:c_seq_ctx. done. rewrite c_seq_assoc. apply:c_seq_ctx. done.

pfold_reverse.
move: c. pcofix C_useless.
intro. pfold.
(*
left. (*move: a c. pcofix CIH. intros.*)

(*2: {  done. }
sum_reshape. 
apply c_co_sum. intros.
simp_premise.*)

pfold. simpl.*)
(* rewrite c_seq_assoc. apply c_seq_ctx. done. *)
apply:c_trans. apply:derive_unfold. apply:c_trans.
2: { apply:c_sym. apply:derive_unfold. } 
apply:c_plus_ctx. done. 
move: (index_enum A) => l'. 
elim: l'. rewrite !big_nil. done. 
intros. rewrite !big_cons. apply:c_plus_ctx;last done.  
clear H. 
apply:c_fix. left. 
(* apply:c_seq_ctx. done. pfold_reverse. *) 
(*(a0 \ Star c, 
   a0 \ (Star c _;_ (Star (Star c)))*)
move: a0.  (*(r0,r1) \in pgfp(bot2)(F)
            (forall (a0 : event) (c : regex), 
            (a0 \ Star c, a0 \ (Star c ; (Star (Star c))) \in R)
            R subset F(R)
               (r0,r1) \in pgfp(R)(F)

*)
pcofix CIH. intros. pfold.
simpl. rewrite c_plus_idemp.
(* apply:c_fix.  

left. move: a0 c. pcofix CIH. intros.*)

(*pfold. simpl.*)
(*apply/CIH.

unfold_tac.
sum_reshape. 
apply c_co_sum. intros.
simp_premise.
left.*)


(*generalize x0. pcofix CIH2. intros.*) (*Coinduction principle*)
(*pfold. *)
(*rewrite c_plus_idemp. *)
rewrite c_seq_assoc. 
 apply c_seq_ctx. done.
apply:c_trans. apply:derive_unfold. apply:c_trans.
2: { apply:c_sym. apply:derive_unfold. } 
apply:c_plus_ctx. done. 
move: (index_enum A) => l'. 
elim: l'. rewrite !big_nil. done. 
intros. rewrite !big_cons. apply:c_plus_ctx;last done.  
clear H. apply:c_fix. right.
apply: CIH.

(*ones := cons 1 ones*)
Qed. 
*)














Inductive contains_gen bisim : regex -> regex -> Prop :=
 contains_con c0 c1 (H0: forall e, bisim (e \ c0) (e \ c1) : Prop ) (H1: nu c0 -> nu c1) : contains_gen bisim c0 c1.
Lemma contains_gen_mon: monotone2 contains_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve contains_gen_mon : paco.



Definition Contains c0 c1 := paco2 contains_gen bot2 c0 c1.
Hint Unfold  Contains : core.

Lemma Contains_der : forall c0 c1, Contains c0 c1 -> forall e,  Contains (e \ c0) (e \ c1).
Proof.
intros. punfold H.  inv H. move: (H0 e). case. done. done.
Qed.

Lemma Contains_nu : forall c0 c1, Contains c0 c1 ->  nu ( c0) -> nu ( c1).
Proof.
intros. punfold H.  inv H. eauto. 
Qed.

(*Definition bisim_proj R r0 r1 (H: bisimilarity_gen R r0 r1) :=
match H with 
| bisimilarity_con _ _ H0 H1 => H0
end.
*)

Definition contains (r0 r1 : regex) := forall s, Match s r0 -> Match s r1.

Theorem containsP : forall c0 c1, contains c0 c1 -> Contains c0 c1.
Proof.
pcofix CIH. intros. pfold. constructor.
- intros. right. apply CIH.  move=> s.  rewrite -!deriveP. eauto.
  move: (H0 nil). rewrite !matchbP /matchb //=. 
Qed.










Inductive D_pi (L : seq pder) : seq pder -> pder -> Prop := 
| pi_stop V l : l \in V ->  D_pi L V l
| pi_next V l : l \notin V -> l \in L -> (forall e, D_pi L (l::V) (pair_pd_l e l))  -> D_pi L V l.



Lemma build_D_pi : forall V l, D_pi (enum_pi2 l) V l.
Proof.



(*Definition pi_rel (L : seq pder) (p0 p1 : ((seq pder) * pder)) := 

Lemma Acc_pi_rel : forall x, Acc (pi_rel (enum_pi x.2)) x.
Proof. 
intros. con. intros. rewrite /pi_rel in H. destruct y. destruct x. 
destruct H. simpl. destruct H0. destruct H1. subst. simpl in H0.

Check Acc_rect.
Check (@Acc_rect _ (pi_rel (enum_pi x.2)))*)


Lemma sub_or_not : forall {A : eqType} (l0 l1 : seq A), is_sub l0 l1 \/ ~ (is_sub l0 l1). 
Proof.
intros. rewrite is_subP. destruct (is_sub_bool _ _)=>//=;eauto.
Qed.

Lemma lt_exists : forall n0 n1, n0 < n1 -> exists n, n + n0 = n1.
Proof.
elim;ssa.
destruct n1;ssa. exists (n1.+1). rewrite addn0. done.
destruct n1;ssa. 
have: n < n1 by lia. move/H. ssa.
exists x. rewrite -H1. lia.
Qed.

Lemma same_size_in : forall (A : eqType) (l0 l1 : seq A), is_sub l0 l1 -> uniq l0 -> size l1 <= size l0 -> is_sub l1 l0.
Proof.
move=> A'. elim. ssa.
de l1.
ssa. 
destruct l1. ssa.
ssa.
have: size l1 <= size l. lia. 
move=> Hsize.
intro. rewrite inE.
destruct (eqVneq x s). subst. simpl. move=>_.
rewrite !inE. destruct (eqVneq s a). done.
simpl.
have: is_sub l l1. intro. intros. 
have: x \in a::l. rewrite !inE H1. lia. 
move/H0. rewrite !inE. move/orP. case.
intros. norm_eqs.

have: is_sub l l1. intro. intros. apply/H0. rewrite !inE H1. lia.
destruct l1.
have: size l1 <= size l. 
intro.
intros. 
rewrite is_subP. destruct (is_sub_bool l1 l0) eqn:Heqn. done. 
move: Heqn. move/negP/negP/allPn. case. ssa.
elim: l1 l0 p q H1 H0 H. done.
move=> a l IH l0.
intros.
rewrite !inE. move/orP. case.
intros. norm_eqs.
have: is_sub l0 l.
intro. move/H. rewrite !inE. move/orP. case;ssa.
norm_eqs.


move=> A'.
elim;ssa. de l1;ssa. 
intro. ssa. destruct l1;ssa. 
inv H2. clear H2.
destruct (eqVneq x a). auto. right.
rewrite !inE in H1. de (orP H1). norm_eqs.
suff: s \in s::l1. 
have: s \in a::l. rewrite !inE. H2. lia. 
move/H0. rewrite !inE. move/orP. case=>//. 
intro. norm_eqs.
suff: x \in s::l1. rewrite !inE.
intros. intro. intros.

Lemma build_D_pi_aux : forall V l, uniq l -> is_sub V (enum_pi l) -> uniq V ->  D_pi (enum_pi l) V l.
Proof. 
intros.
destruct (sub_or_not (enum_pi l) V). con. apply/H2. apply/enum_pi_self. done.
move: H2. rewrite is_subP /is_sub_bool.
move/negP. move/allPn. case.
simpl. intros.
have: size V < size (enum_pi l). apply:size_strict_sub. done. 
simpl.  eauto. eauto. done.
clear p q x.
move/lt_exists. case.
elim. rewrite add0n. intro. con. 

Search _ (_ < _).c
Check size_strict_sub.

intros.
 have : Acc pi_rel (V,l).





Lemma pi_pi : forall r0 r1 r2, r1 \in pi r0 -> r2 \in pi r1 -> r2 \in pi r0.
Proof.
elim;ssa.
- rewrite !inE in H. norm_eqs. ssa.
- rewrite mem_cat in H1. de (orP H1). 
  move: (H _ _ H3 H2). ssa.  rewrite mem_cat H4 //.
  move: (H0 _ _ H3 H2). ssa. rewrite mem_cat H4 //. lia.
- rewrite mem_cat in H1. de (orP H1). de (mapP H3). subst. ssa.
  rewrite mem_cat in H2. lo. de (mapP H5). subst.
  move: (H _ _ H4 H6). ssa. 
  rewrite mem_cat. apply/orP. left. apply/map_f. done.
  rewrite mem_cat H5. lia.
  move: (H0 _ _ H3 H2). ssa. rewrite mem_cat. apply/orP. eauto.
- de (mapP H0). subst. ssa. rewrite mem_cat in H1. lo. de (mapP H3). subst.
  move: (H _ _ H2 H4). ssa.
  eauto. apply/map_f. done.
Qed.





Inductive bisiml_gen bisim : (seq regex) -> (seq regex) -> Prop :=
 bisiml_con l0 l1 (H0: forall e, bisim (pd_l e l0) (pd_l e l1) : Prop ) (H1: has nu l0 = has nu l1) : bisiml_gen bisim l0 l1.

Definition Bisiml l0 l1 := paco2 bisiml_gen bot2 l0 l1.
Hint Unfold  Bisiml : core.

Lemma bisiml_gen_mon: monotone2 bisiml_gen. 
Proof.
unfold monotone2. intros.  constructor. inversion IN. intros.
auto. inversion IN. auto.  
Qed.
Hint Resolve bisiml_gen_mon : paco.





Definition pder := seq

Definition pi_l l := undup (flatten (map pi l)).

(*Lemma pi_l_size : forall l, size (pi_l l) <=*)

Fixpoint all_pder_aux n (l : pder) := 
match n with 
| 0 => nil::nil 
| n'.+1 => (compose l (all_pder_aux n' l) cons) ++ (all_pder_aux n' l)
end.

Lemma all_pder_aux_nil : forall n l, [::] \in all_pder_aux n l.
Proof.
elim;ssa. rewrite mem_cat H. lia.
Qed.
Hint Resolve all_pder_aux_nil.
Lemma in_all_pder_aux : forall n l' l, size l <= n -> (forall x, x \in l -> x \in l') -> l \in (all_pder_aux n l').
Proof.
elim;ssa. 
destruct l;ssa. 
destruct l;ssa.
rewrite mem_cat. apply/orP. right. done.
rewrite mem_cat. apply/orP. left. apply/mem_compose. eauto. eauto.
Qed.

Definition all_pder l := all_pder_aux (size (pi_l l)) (pi_l l).


Lemma in_all_pder_size : forall n l l', l' \in all_pder_aux n l -> size l' <= n.
Proof.
elim;ssa. rewrite !inE in H. norm_eqs. done.
rewrite mem_cat in H0. lo. apply mem_compose_cons in H1. ssa. subst. ssa. eauto.
eauto.
Qed.

Lemma self_all_pder_aux : forall n l, size l <= n -> l \in all_pder_aux n l.
Proof.
intros. apply:in_all_pder_aux. done. eauto.
Qed.

(*Lemma pd_pi_sub : forall l a,  subseq (undup (pd a l)) (undup (pi l)).
Proof.*)

Lemma count_undup_sub : forall (B : eqType) (l l' : seq B), (forall x, x \in l -> x \in l')  ->  size (undup l) <= size  (undup l').
Proof. 
move=> B.
elim;ssa. case_if. eauto. 
ssa.
have : (forall x, x \in l -> x \in filter (fun y => y  != a) l'). 
intros. rewrite mem_filter. ssa.  apply/eqP. intro. subst. rewrite H1 in H2. done.  
move/H. move=>HH.
have: (size (undup l)).+1 <= (size (undup [seq y <- l' | y != a])).+1. lia.
intros.
apply:leq_trans.  apply: H2. 
Unset Printing Notations.
apply/HH.
apply/H0. rewrite !inE H2. lia.


have : (forall x, x \in l -> x \in rem a l'). 
intros. rewrite mem_rem //. apply/eqP. intro. subst. rewrite H1 in H2. done.  apply/H0. rewrite !inE H2. lia.
move/H. Search _ rem.
destruct l';ssa. move: (H0 a). rewrite !inE. ssa.
case_if. 
admit.
ssa.
suff: size (undup l) <= size (undup l'). lia.
destruct (eqVneq s a). subst.
apply/H.  intros. move: (H0 x). rewrite !inE H3 orbC /=. move/(_ is_true_true).
move/orP. case. intros. norm_eqs. rewrite H1 in H3. done. done.
apply:H. 
intros. move: (H0 x). rewrite !inE H orbC /=. move/(_ is_true_true). 
move/orP. case. intros. norm_eqs. rewrite H1 in H.
intros. move: (H0 x).  rewrite inE.
rewrite !inE H3 orbC /=.  rewrite H /=. 
move/(_ is_true_true). move/orP. case. intros. norm_eqs.
move: (H0 a). rewrite !inE H1 .
have: (forall x, x \in l -> x \in l'). eauto. 
move/H.  intros. lia.
lia.
Admitted.

Lemma size_pd_l_pi_l : forall l a, size (pd_l a l) <= size (pi_l l).
Proof.
rewrite /pd_l /pi_l.
intros. Search _ (size (undup _)).
elim;ssa. rewrite !undup_cat !size_cat. 
have: forall (n0 n1 n2 n3 : nat), n0 <= n2 -> n1 <= n3 -> n0 + n1 <= n2 + n3. lia.
intros. apply/H0;eauto. 
rewrite !size_filter /=. clear H0 H.
have:  count (fun x : regex => x \notin flatten [seq pd a0 i | i <- l])
    (undup (pd a0 a)) <=  count (fun x : regex => x \notin flatten [seq pd a0 i | i <- l])
    (undup (pi a)). apply/count_undup_sub.
intros. apply:pi_d. eauto. 
intros. apply:leq_trans. eauto. apply:sub_count. 
intro. ssa. apply/negP. intro. move/negP: H0. intro. apply/H0. 
de (flattenP H1). de (mapP H2). subst.
apply/flattenP. simpl. econ. apply/mapP. econ. eauto. 2: eauto. done.
Search _ (count _ _ <= count _ _).
Check count_undup.
suff: size [seq x <- undup (pd a0 a) | x \notin flatten [seq pd a0 i | i <- l]] <=   size [seq x <- undup (pi a) | x \notin flatten [seq pi i | i <- l]].
lia.
 Check size_undup.
sim

Lemma size_pi_pd : forall l l' a, l' \in all_pder l -> size (pd_l a l') <= size (pi_l l).
Proof. simpl. intros. 
apply/in_all_pder_size.
apply in_all_pder_size in H. apply self_all_pder_aux in H.
apply in_all_pder_size in H.
move: (self_all_pder_aux n l').
lia.
move: (in_all_pder_size  H).



Lemma all_pder_closed : forall l l' a, l' \in all_pder l -> pd_l a l' \in all_pder l.
Proof.
intros. apply/in_all_pder_aux. lia.


Lemma in_pi_l : forall l r1 r2 a, r1 \in pi_l l -> r2 \in pd a r1 -> r2 \in pi_l l.
Proof.
intros. destruct (flattenP H). ssa. de (mapP H1). subst. 
Check in_pi. 
move: (in_pi _ _ _ _ H2 H0). ssa. 
apply/flattenP. econ. apply/map_f. eauto. done.
Qed.

(*Lemma pi_pi_l : forall l r1 r2 a, r1 \in pi_l l -> r2 \in pi_l l -> r2 \in pi_l l.*)











Inductive ACI : regex -> regex -> Prop :=
| ACI_r c : ACI c c
(*| ACI_A c0 c1 c2 : ACI ((c0 _;_ c1) _;_ c2) (c0 _;_ (c1 _;_ c2))*)
| ACI_AP c0 c1 c2 : ACI ((c0 _+_ c1) _+_ c2) (c0 _+_ (c1 _+_ c2))
(*| ACI_C c0 c1  : ACI (c0 _+_ c1) (c1 _+_ c0)*)
(*| ACI_I c  : ACI c (c _+_ c)*)
(*| ACI_sym c0 c1 : ACI c0 c1 -> ACI c1 c0*)
| ACI_t c0 c1 c2 : ACI c0 c1 -> ACI c1 c2 ->  ACI c0 c2
| ACI_p c0 c1 c2 c3 : ACI c0 c2 -> ACI c1 c3 ->  ACI (c0 _+_ c1) (c2 _+_ c3).
(*| ACI_s c0 c1 c2 c3 : ACI c0 c2 -> ACI c1 c3 ->  ACI (c0 _;_ c1) (c2 _;_ c3).*)
(*| ACI2 c : ACI Empt (Empt _;_ c)*)
(*| ACI3 c: ACI Empt (Empt _;_ c)*)
(*| ACI4 c: ACI c (Empt _+_ c)*)
(*| ACI5 c: ACI (Empt _+_ c) c.*)

(*| ACI_dist c0 c1 c2: ACI ((c0 _+_ c1) _;_ c2) (c0 _;_ c2 _+_ c1 _;_ c2).*)
(*| ACI_dist2 c0 c1 c2: ACI (c0 _;_ (c1 _+_ c2) ) (c0 _;_ c1 _+_ c0 _;_ c2)*)
Hint Constructors ACI.







(*Lemma in_pi : forall r0 r1 r2 a, r1 \in pi r0 -> r2 \in pd a r1 -> exists x, r2 = x /\ x \in pi r0.
Proof.
elim;ssa.
- rewrite !inE in H. norm_eqs. ssa. 
- rewrite !mem_cat in H1 *.  destruct (orP H1).  
  move: (H _ _ _ H3 H2). ssa. econ. con. apply:H4. rewrite mem_cat H5. lia.
  move: (H0 _ _ _ H3 H2). ssa. econ. con. apply:H4. rewrite mem_cat H5. lia.
- rewrite !mem_cat in H1 *. 
  destruct (orP H1). destruct (mapP H3). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H2. destruct (orP H2).
  destruct (mapP H5). subst. 
  move: (H _ _ _ H4 H6). ssa.
  exists (x1 _;_ r1). con. eauto. subst. done. rewrite mem_cat. apply/orP.  left. apply/map_f. done.
  econ. con. econ. rewrite mem_cat. apply/orP. right. eauto.
  destruct (mapP H2). subst. 
  move: (H _ _ _ H4 H5). ssa.
  exists (x1 _;_ r1). ssa. subst. done. rewrite mem_cat. apply/orP. left. apply/map_f. eauto.
  move: (H0 _ _ _ H3 H2). ssa.  
  econ. con.  apply/H4. 
  rewrite mem_cat H5.  lia.
- destruct (mapP H0). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H3). subst.
  move: (H _ _ _ H2 H4). ssa.
  exists (x1 _;_ Star r0). con. subst. done. eauto. 
  apply/map_f. eauto.
  destruct (mapP H3). subst.
  econ. con. econ. apply/map_f. eauto.
  destruct (mapP H1). subst. ssa.
  move: (H _ _ _ H2 H3). ssa.
  exists (x1 _;_ Star r0). con. eauto.  subst. done.
  apply/map_f. eauto.
Qed.*)

(*Lemma in_pi : forall r0 r1 r2 a, r1 \in pi r0 -> r2 \in pd a r1 -> exists x, ACI r2 x /\ x \in pi r0.
Proof.
elim;ssa.
- rewrite !inE in H. norm_eqs. ssa. 
- rewrite !mem_cat in H1 *.  destruct (orP H1).  
  move: (H _ _ _ H3 H2). ssa. econ. con. apply:H4. rewrite mem_cat H5. lia.
  move: (H0 _ _ _ H3 H2). ssa. econ. con. apply:H4. rewrite mem_cat H5. lia.
- rewrite !mem_cat in H1 *. 
  destruct (orP H1). destruct (mapP H3). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H2. destruct (orP H2).
  destruct (mapP H5). subst. 
  move: (H _ _ _ H4 H6). ssa.
  exists (x1 _;_ r1). con. eauto. rewrite mem_cat. apply/orP.  left. apply/map_f. done.
  econ. con. apply/ACI_r. rewrite mem_cat. apply/orP. right. eauto.
  destruct (mapP H2). subst. 
  move: (H _ _ _ H4 H5). ssa.
  exists (x1 _;_ r1). ssa. rewrite mem_cat. apply/orP. left. apply/map_f. eauto.
  move: (H0 _ _ _ H3 H2). ssa.  
  econ. con.  apply/H4. 
  rewrite mem_cat H5.  lia.
- destruct (mapP H0). subst. ssa.
  destruct (nu _) eqn:Heqn.   rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H3). subst.
  move: (H _ _ _ H2 H4). ssa.
  exists (x1 _;_ Star r0). con. eauto. 
  apply/map_f. eauto.
  destruct (mapP H3). subst.
  econ. con. apply:ACI_r. apply/map_f. eauto.
  destruct (mapP H1). subst. ssa.
  move: (H _ _ _ H2 H3). ssa.
  exists (x1 _;_ Star r0). con. eauto. 
  apply/map_f. eauto.
Qed.
Ltac lfin :=   econ; con; [ apply:ACI_r | done].*)








(*Let o_eqs := (o_plus,o_seq,o_true,o_false).*)

(*Definition ex_eq {A : eqType} (l: seq A) (F0 F1 : A -> regex) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus : forall (l : seq A) F1 F2 (R: regex -> regex -> Prop), ex_eq l F1 F2 (c_eqc R) ->
   \big[Plus/Empt]_(i <- l) F1 i =( R )= \big[Plus/Empt]_(i <- l) F2 i.
Proof.
move=> + F1 F2 R. 
rewrite /ex_eq. elim=>//.
move=> _. rewrite !big_nil//.
move=> a l IH Hin. rewrite !big_cons. rewrite Hin //. 
eq_m_left.
Qed.

(*Necessary to use ssreflect under for rewriting*)
Add Parametric Morphism R : (Under_rel regex (c_eqc R)) with
signature (c_eqc R ==> c_eqc R ==> flip impl) as under_c_eqc. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''. apply/c_trans.  eauto. apply/c_trans. eauto. apply/c_sym. eauto.
Qed.

Add Parametric Morphism R : (Under_rel regex (c_eqc R)) with
signature (c_eqc R ==> c_eqc R ==> impl) as under_c_eq. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''.  apply/c_trans;last by eauto. apply/c_trans;last by eauto. apply/c_sym. eauto.
Qed.

(*This has to be proved by induction because I cannot use ssreflects big_split since commutativity is over c_eqc, and not leibniz equality*)
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
Lemma star_o : forall R c c', Star ((o c) _+_ c') =(R) = Star c'.
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
  rewrite {1}star_o.
  rewrite {1}star_o. 
  rewrite c_unfold. done.
 (*We need c_star_plus here*)
Qed.*)

(*Lemma big_shape: forall c, \big[Plus/Empt]_a (Event a _;_ a \ c) = \big[Plus/Empt]_(i <- map (fun a => (a,a\c)) (index_enum A)) (Event i.1 _;_  i.2).
Proof.
move=> c. move Heq: (index_enum _)=>ef. clear Heq.
elim: ef. rewrite !big_nil //.
move=> a l IH. rewrite !big_cons /=. f_equal. done.
Qed.*)


(*Lemma bisim_completeness : forall c0 c1, Bisimilarity c0 c1 -> EQ c0 c1.
Proof. Admitted.
(*pcofix CIH.
intros. punfold H0. inversion H0.
pfold. rewrite (derive_unfold _ c0) (derive_unfold _ c1). subst.
rewrite /o H2.
suff:    \big[Plus/Empt]_a (Event a _;_ a \ c0) = (upaco2 c_eqc r)=
  \big[Plus/Empt]_a (Event a _;_ a \ c1). move=> HH.
 case Hcase:(nu _)=>//. eq_m_left. eq_m_left.

move: (index_enum _)=>ef. elim: ef=>//. rewrite !big_nil //.
move=> a l HQ/=. rewrite !big_cons. apply/c_plus_ctx=>//.
apply/c_fix=>/=. right. apply/CIH. case: (H1 a)=>//.
Qed.*)

Theorem soundness : forall c0 c1, EQ c0  c1 -> (forall s, Match s c0 <-> Match s c1).
Proof.
move=>c0 c1 /bisim_soundness/equivP=>//. 
Qed.

Theorem completeness : forall c0 c1, (forall s, Match s c0 <-> Match s c1) -> EQ c0 c1.
Proof.
intros. apply bisim_completeness. apply/equivP=>//.
Qed.*)





(*Lemma test a c: (c_eqc (c_eqc bot2) (Event a _;_ c) (Event a _;_ c)).
Proof.
apply:c_fix. *)

(*




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



*)

(*From Coq.Logic Require Import Eqdep_dec.


Module DSL_mod : DecidableSet.
Definition U := dsl.
Lemma U_eq : U = dsl.
Proof. done. Qed.
Definition eq_dec : forall x y:U, {x = y} + {x <> y}.
Proof. intros. case: (eqVneq x y). auto. move/eqP. eauto.
Qed.
End DSL_mod.

Import DSL_mod.
Check eq_proofs_unicity_on.
Module EqDep := Coq.Logic.Eqdep_dec.DecidableEqDepSet DSL_mod. 
Import EqDep.

Lemma test : DSL_mod.U = dsl.
Proof. Locate U_eq.
done.
*)



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

 (**)
(*Variable (As : Set).
Hypothesis (H : Finite.axioms_ As).
Definition A : finType := @Finite.Pack As H.
Check @Finite.Pack.
Check (Finite.sort A).
Check A.*)

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

(*Lemma Match_big_undup_cat : forall l  l' s, Match s (\big[Plus/Empt]_(i <- undup (l ++ l')) i)  <->  Match s ((\big[Plus/Empt]_(i <- undup l) i) _+_  (\big[Plus/Empt]_(i <- undup l') i)).
Proof.
elim;ssa. rewrite !big_nil. split. intros. constructor 5. 
elim: l' H. ssa. 
ssa. 
Admitted.*)
(*move: H0. case_if. ssa. rewrite big_cons. eauto. 
rewrite !big_cons /=. intros. inv H1. eauto. eauto.
intros. inv H. inv H2. 
clear H. elim: l' H2;ssa.
rewrite !big_cons in H2. 
case_if.  inv H2.
inv H2.*)



(*Lemma BisimInd_sym : forall l l', BisimInd l l' -> BisimInd l' l.
Proof.
pcofix CIH. intros. punfold H0. inv H0. pfold. con. right. apply/CIH. 
de (H1 e). lia.
Qed.

Lemma BisimInd_trans : forall l0 l1 l2, BisimInd l0 l1 -> BisimInd l1 l2 -> BisimInd l0 l2.
Proof.
pcofix CIH.
intros. punfold H0. inv H0. punfold H1. inv H1. pfold. con. intros.
destruct (H2 e);ssa. destruct (H4 e);ssa. right. eauto. 
lia.
Qed.

Theorem Bisim_ind_co : forall l l', BisimInd l l' ->  Bisimilarity (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i).
Proof.
pcofix CIH. intros. punfold H0. inv H0. pfold. con. intros.
right. rewrite !big_derive. apply:CIH.
destruct (H1 e)=>//. rewrite /pd_l in H.
apply/equivP. move/equivP : H.
intros.
apply:equiv_r_trans. apply/equiv_r_sym. apply:derive_pd_l.
apply:equiv_r_trans.  done.
apply:derive_pd_l.
rewrite !nu_has in H2. done.
Qed.

Theorem equiv_BisimInd : forall l l', equiv (\big[Plus/Empt]_(i <- l) i) (\big[Plus/Empt]_(i <- l') i) -> BisimInd l l'.
Proof.
intros.  move/equivP/Bisim_co_ind : H=>//. 
Qed.*)




(*Lemma pi_test : forall (l : seq regex) a, (pd_l a l) \in  enum_pi l.
Proof.
intros. apply:in_enum_uniq. rewrite /pd_l. apply:undup_uniq.
intros. rewrite /pd_l in H. rewrite mem_undup in H. de (flattenP H). 
de (mapP H0). subst. rewrite /pi_l. rewrite mem_undup.
apply/flattenP. simpl. econ. apply:map_f. 2: { rewrite !inE. apply/orP. right.
apply:pi_d. apply:H1. }  done.
Qed.*)

(*eapply enum_pi_pd_l in H1 as HX. ssa. 2:eauto.*)

(*clear H1. rewrite /enum_pi in H2.
Check enum_inR. *)



(*Lemma pi_test2 : forall (l l' : seq regex) a, l' \in  enum_pi l -> pd_l a l' \in enum_pi l.
Proof.
intros. apply:in_enum_uniq. rewrite /pd_l. apply:undup_uniq.
intros. rewrite /pd_l in H0. rewrite mem_undup in H0. de (flattenP H0). clear H0.
de (mapP H1). clear H1. subst. rewrite /pi_l. rewrite mem_undup. 
apply/flattenP. simpl. rewrite /enum_pi in H.
move: (@enum_inR _ _ _ l' x1 H H0). move=> Hin. rewrite /pi_l in Hin. rewrite mem_undup in Hin.
de (flattenP Hin). de (mapP H1). subst. 
econ. apply:map_f. 2: { apply:in_pi2. 2: eauto. eauto. }  
done.
Qed.*)

(*Lemma pi_test3 : forall l l' a,  l' \in enum_pi (pd_l a l) ->  l' \in enum_pi l.
Proof.
intros.*)
Check in_enum_uniq.
(*Equations bisim (pp : pder * pder) (visited : seq (pder * pder) ) (H : uniq_pair pp) : bool by wf (r_measure visited pp) := 
 bisim pp visited H  with (dec (pp \in visited)) => {
  bisim _  _ _ (in_left) := true;
  bisim pp visited _ (in_right) := ((has nu pp.1) == (has nu pp.2)) && 
                                           (foldInAll (index_enum A) (fun e _ => bisim (pair_pd_l e pp) (pp::visited) _));
 }.
Next Obligation. 
apply/andP.
con. simpl. rewrite /pd_l. done.  simpl. rewrite /pd_l. done.
Defined.
Next Obligation.
apply/ltP. apply:measure_lt. done. rewrite e0 //. 
Defined.*)

(*Lemma uniq_pair_proof : forall  l l', uniq_pair (undup l,undup l').
Proof.
intros. apply/andP. con; ssa. 
Qed.*)




Check bisim.

(*
Lemma bisim_sound_aux : forall e0 e1 l_v (R : lType -> lType -> Prop), (forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   bisim (e0,e1) l_v -> upaco2 ((ApplyF full_eunf full_eunf \o EQ2_gen)) R e0 e1. 

*)




(*Lemma derive_star_bad : forall E F, dsl nil E F -> dsl nil (Star E) (Star F).
Proof.
intros. apply:dsl_fix.
apply:ctrans. apply:wrapinv. apply:ctrans. apply:cplus. 
apply:cid. apply:cseq. apply:cid.
apply:dsl_var. done. 
apply:ctrans. apply:cplus. apply:cid. apply:cseq. apply:dsl_mon. apply:X. apply:cid.
apply:wrap.
Defined.*)

(*Print derive_star_bad.*)

(*Lemma derive_star_bad : forall E F, dsl nil E F -> dsl nil (Star E) (Star F).
Proof.
intros. apply:dsl_fix.
apply:ctrans. apply:wrapinv. apply:ctrans. apply:cplus. 
apply:cid. apply:cseq. apply:dsl_mon. apply:X.
apply:dsl_var. done. 
apply:wrap.*)


(*Arguments p_inl {r0 r1}.
Arguments p_inr {r0 r1}.
Arguments p_pair {r0 r1}.
Arguments p_fold {r}.*)

(*Arguments pt_inl {r0 r1 p}.
Arguments pt_inr {r0 r1 p}.
Arguments pt_pair {r0 r1 p0 p1}.
Arguments pt_fold {r p}.
Hint Constructors typing.*)



(*Definition take_my_fix2  (f : forall p, (forall p', upRel p' p -> upTree) -> upTree) : upTree -> upTree := 
fun T => fix my_fix (H : D_fix (f) {struct H} := f (my_fix (proj H))*)


(*f (take_mu_fix2 f)

 f p (fun p' => take_fix_fuel3 n' p' f)

Fixpoint take_my_fix (p : upTree) (f : (forall p', upRel p' p -> upTree) -> upTree -> upTree) {struct p} : upTree -> upTree.
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
Eval compute in (take_fix_fuel2 2 test_f (up_pair up_tt up_tt)). *)


(*Eval compute in (take_fix_fuel3 4 (up_pair up_tt up_tt) test_f).*)


(*Fixpoint take_fix_fuel2 (f : forall p, (forall p', upRel p' p -> upTree) -> upTree) : (upTree -> upTree).*)


(*Fixpoint take_fix_fuel n (f : (upTree -> upTree) -> upTree -> upTree) : (upTree -> upTree) :=


 (f : forall p', upTree_0size p' < upTree_0size p -> upTree) : upTree := 


Definition take_fix (p : upTree) (f : forall p', upTree_0size p' < upTree_0size p -> upTree) : upTree := *)


(*Section size_eliminator_for_upTree.
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
*)


(*Lemma test : forall (P : upTree -> Type), (forall p, (forall p', upTree_0size p' < upTree_0size p -> P p') -> P p) -> forall (p : upTree), P p.
Proof.
move=> P Hsize p. move Heq: (upTree_0size p) => n. move: n p Heq.
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


Definition my_fix (f : (forall u, (forall u' : upTree, upRel u' u -> upTree) -> upTree)) :  upTree -> upTree:=
(upTree_0size_rect (fun _ => upTree) f).

Lemma sum_bool p p' :  {upRel p p'} + { ~ upRel p p'}.
Proof. rewrite /upRel. case Heq : (_ <_)=>//. con. done. right. intro. done.
Defined.

Definition test u : (forall u' : upTree, upRel u' u -> upTree) -> upTree  := 
fun f => match u with 
       | up_pair u0 u1 => match sum_bool u0 u with 
                          | left p => f _ p
                          | right p => u
                          end
       | _ => u
       end.

(*Fixpoint interp d (f : (forall u, (forall u' : upTree, upRel u' u -> upTree) -> upTree)) :  upTree -> upTree  := 
match d with 
| cfix d' => my_fix (interp d')
| cguard (var_dsl 0) => *)


Definition myP (p : upTree) :=  (forall p', upRel p' p -> upTree) -> upTree.

Definition guarded_fun u := (forall u' : upTree, upRel u' u -> upTree) -> upTree.





(*Lemma Acc_pRel :  forall p, Acc pRel p.
Proof. 
move=> p. move Heq : (upTree_0size p)=>n. elim: n p Heq.
case=>//. move=> n IH. case;intros. con;intros. 
move: H. rewrite /pRel. simpl.  move: (upTree_1size1 y). lia.
con. intros. move: H. rewrite /pRel. simpl. move: (upTree_1size1 y). lia.
con. intros. move: H. rewrite /pRel. simpl. move: (upTree_1size1 y). lia.
move: Heq. simpl. case. intro. 
con. intros. apply/IH.
intros. apply/IH.
intros.
rewrite /pRel //=.
inv H.

simpl. simpl. repeat simpl.
con. move=> y.*)


(*Fixpoint take_fix_fuel n (f : (upTree -> upTree) -> upTree -> upTree) : (upTree -> upTree) :=
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
end.*)

(*Eval compute in (take_fix_fuel3 0 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel3 1 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel3 2 (up_pair up_tt up_tt) test_f).
Eval compute in (take_fix_fuel2 2 test_f (up_pair up_tt up_tt)). *)


(*Check @Acc_rect.
Check (@Acc_rect upTree pRel (fun p => (forall p', pRel p' p -> upTree) -> upTree -> upTree)).

Check upTree_rect.
*)



(*Definition higher_n (n : nat) := (forall p', upTree_0size p' < n -> upTree) -> upTree -> upTree.

Inductive D_fix (n : nat) : higher_n n -> Prop :=
| D_next n n' f : n' < n -> D_fix f  -> D_fix f.
*)




(*Inductive D_dom l  : forall r0 r1, nat -> dsl l r0 r1 ->  Prop :=
| D_fix n r0 r1 (p : dsl ((r0,r1)::l) r0 r1)  : D_dom n p -> D_dom n.+1 (dsl_fix p)
| D_trans n r0 r r1  (p0: dsl l r0 r) (p1 : dsl l r r1) : D_dom n p0 -> D_dom n p1 -> D_dom n (ctrans p0 p1)
| D_plus n r0 r1 r0' r1'  (p0: dsl l r0 r1) (p1 : dsl l r0' r1') : D_dom n p0 -> D_dom n p1 -> D_dom n (cplus p0 p1)
| D_seq n r0 r1 r0' r1'  (p0: dsl l r0 r1) (p1 : dsl l r0' r1') : D_dom n p0 -> D_dom n p1 -> D_dom n (cseq p0 p1).
Ltac pt := auto with pauto.
Print inv.
Ltac invc H := inversion_clear H; subst; try done.
Ltac ipt := intros;repeat 
            match goal with 
             | [ H : pTree (_ _+_ _) |- _] => invc H;pt
             | [ H : pTree (_ _;_ _) |- _] => invc H;pt
             | [ H : pTree Empt |- _] => invc H;pt
            end.*)

(*Require Import Coq.Classes.EquivDec.
#[global]
Instance reg_eq_eqdec : EqDec regex eq. 
rewrite /EqDec. intros. rewrite /equiv /complement.
case:(eqVneq x y);auto. move/eqP. eauto.
Defined.*)

(*Definition dsl_proj2 : forall (x : regex) (P : regex -> Type) (y y' : P x), existT P x y = existT P x y' -> y = y' :=
(@EqDec.inj_right_pair _ reg_eq_eqdec).*)


(*Definition proj_fix n l (r0 r1: regex) (p: dsl ((r0,r1)::l) r0 r1)  
           (D : D_dom n.+1 (dsl_fix p)) : D_dom n p.
inv D.
do ? apply dsl_proj2 in H2. subst. done.
Defined.*)



(*Definition proj_fix0 l (r0 r1: regex) (p: dsl ((r0,r1)::l) r0 r1)  
           (D : D_dom 0 (dsl_fix p)) : False.
inv D.
Defined.*)

(*Lemma pTree_0size_rect
     : forall P : forall r, pTree r -> Type,
       (forall r (u  : pTree r), (forall u' : pTree r, pRel u' u -> P r u') -> P r u) ->
       forall r (p : pTree r), P r p.
Proof.
move=> P  Hsize r u. 
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
Defined.*)
(*Notation "c0 <T= c1" := ((pTree c0) -> (pTree c1))(at level 63).*)
(*Definition guard_i a A' B (f : A' <T= B) : ((Event a) _;_ A') <T= ((Event a) _;_ B). 
intro. inv X. con. apply:X0. apply:f. apply:X1.
Defined.*)

(*Definition non_expan (A' B : regex) (f : A' <T= B) := forall T, pTree_0size (f T) <= pTree_0size T.*)


(*Lemma nat_refl : forall (x : nat) (H: x = x), H = @Logic.eq_refl nat x.
Proof.
intros. apply: eq_proofs_unicity. apply:dec_nat.
Qed.
Lemma interp_star_none_pair : forall n d d' T0 T1 (Heq : full_unf d = cstar d') (D: D_dom d' n),
    interpl D T0 = None ->
    interpl (D_star d Heq D) (up_fold (up_inr (up_pair T0 T1))) = None.
Proof.
intros. unlock interpl. simpl. 
(*move: Heq.*)
 (*erewrite Heq. *) 
move: (@Logic.eq_refl _ (full_unf _)). (*The match is applied on an eq_refl, say H, proof, generalize H *)
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: Heq2. rewrite Heq. move=>H2. 
rewrite (dsl_refl H2). unlock interpl in H. rewrite H //.
Qed.
*)

(*Fixpoint interp l r0 r1 (p : dsl l r0 r1) {struct p}:
   forall (T : pTree r0 -> (f : forall x y, (x,y) \in l -> pTree x -> pTree y)  pTree r1.
refine(
match p in dsl _ x y return r0 = x -> r1 = y ->  pTree r0 -> pTree r1  with
| dsl_fix r0 r1 p0 => fun HQ HQ' => _
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
all:intros;subst.
all:try solve.
31: { inv X. con. done. eauto. Guarded. }
31: { move: X. 
apply (@pTree_0size_rect r0 (fun (p : pTree r0) => pTree r1)).
intros. eapply interp. 3:apply u. apply p0. 
intros.  rewrite !inE in H. destruct (eqVneq (x,y) (r0 ,r1)). inv e.
eapply X. instantiate (1:=X0).*)




























Lemma guard_size a (A' B : regex) (f : A' <T= B) : non_expan f  -> forall T, pTree_0size (@guard_i a _ _  f T) <= pTree_0size T.
Proof.
move=>Hnon. intros. 
rewrite /guard_i. dependent destruction T.   simpl. 
move: (Hnon T2). lia.
Defined.

Fixpoint interp l r0 r1 (p : dsl l r0 r1) (T : pTree) (f : forall x y, (x,y) \in l -> { f : pTree x -> pTree y | non_expan f}) {struct p}:
   { f : pTree r0 -> pTree r1 | non_expan f}.
refine(
match p in dsl _ x y return r0 = x -> r1 = y ->  { f : pTree r0 -> pTree r1 | non_expan f}  with
| dsl_fix r0 r1 p0 => fun HQ HQ' => _
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
all:intros;subst.
all:try solve.
31: { move: (f _ _ i). case. intros.
      exists (guard_i x). intros. apply:guard_size. done. } 
31: {

Fixpoint interp l r0 r1 (p : dsl l r0 r1) (f : forall x y, (x,y) \in l -> { f : pTree x -> pTree y | non_expan f}) {struct p}:
   { f : pTree r0 -> pTree r1 | non_expan f}.
refine(
match p in dsl _ x y return r0 = x -> r1 = y ->  { f : pTree r0 -> pTree r1 | non_expan f}  with
| dsl_fix r0 r1 p0 => fun HQ HQ' => _
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
all:intros;subst.
all:try solve.
31: { move: (f _ _ i). case. intros.
      exists (guard_i x). intros. apply:guard_size. done. } 
31: {

eapply interp.  apply p0. intros.
 move: (interp _ _ _ p0). move

move: X. 
apply (@pTree_0size_rect (fun r (p : pTree r) => pTree r1)).
move=> r.
      intros. move: u X.


Fixpoint interp l r0 r1 (p : dsl l r0 r1) (f : forall x y, (x,y) \in l -> (pTree x -> pTree y)) {struct p}:
   pTree r0 -> pTree r1.
refine(
match p in dsl _ x y return r0 = x -> r1 = y -> pTree x -> pTree y  with
| dsl_fix r0 r1 p0 => fun HQ HQ' => _
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
all:intros;subst.
all:try solve.
31: { intros. inv X. con. done. apply:f. eauto. done. }
31: { move: X. apply (@pTree_0size_rect (fun r (p : pTree r) => pTree r1)).
      intros. move: u X.
eapply interp. apply p0.
      intros. 
      rewrite !inE in H. destruct (eqVneq (x,y) (r0,r1)). ssa. inv e. 
      move: (@X X0).
eapply X.
      instantiate (1:= X0).
      eapply X. 2: eauto.
apply IH. apply X.
move Heqn: (pTree_0size X) =>n. have: pTree_0size X < n.+1. rewrite Heqn //.
      clear Heqn. move=>Hfuel.
 move: X. fix IH 1. eapply interp. apply p0. intros. 
      rewrite !inE in H. destruct (eqVneq (x,y) (r0,r1)). ssa. inv e. apply IH. apply X.
      simpl in H. eapply f. apply H. apply X. Guarded.
 move Heqn : (pTree_0size X)=>n.  move: X. 
(*move: (@interp _ _ _ _ _ _ p0).*)
eapply interp. apply:p0.
intros.
rewrite !inE in H. destruct (eqVneq (x,y) (r0,r1)). inv e. ssa. clear H p. clear e. 
(*      clear e H p.  (*move: (interp _ _ _ p0)=>Hl. *) *) clear X.
      move: r0 r1 X0 p0.
      fix IH 3.
      move=> r0 r1. case; intros. 
      
inversion p0;subst;eauto.
      elim.
      apply:Hl
      simpl in H. apply:f. eauto. apply:X.
apply:interp. apply:p0.





Fixpoint interp n 

Fixpoint interp l r0 r1 (p : dsl l r0 r1) (f : forall x y, (x,y) \in l ->  (pTree x -> pTree y)) 
 {struct D}:
   pTree r0 -> pTree r1.
case: p D;intros;try solve [clear f; ipt | clear f;pt].
4: {  inv X. con. done. apply:f. eauto. done. } 
4: { destruct n. apply proj_fix0 in D. done. 
     apply proj_fix in D. move: D X.
     fix IH 1. intros. 
apply proj_fix in D.
move:d X.



l r0 r1 (p : dsl l r0 r1) (f : forall x y, (x,y) \in l -> (pTree x -> pTree y)) (D: D_dom n p)
 {struct D}:
   pTree r0 -> pTree r1.
case: p D;intros;try solve [clear f; ipt | clear f;pt].

move: (proj_trans0 D)=>Hd.
move: (proj_trans1 D)=>Hd1.
eapply interp. apply:f. apply:Hd1. 
eapply interp. apply:f. apply:Hd. apply:X.

move: (proj_plus0 D)=>Hd.
move: (proj_plus1 D)=>Hd1.
move: (@interp _ _ _ _ _ f Hd)=>Ht.
move: (@interp _ _ _ _ _ f Hd1)=>Ht1.
inv X. 
apply:p_inl. apply:Ht. apply:X0.
apply:p_inr. apply:Ht1. apply:X0.

move: (proj_seq0 D)=>Hd.
move: (proj_seq1 D)=>Hd1.
move: (@interp _ _ _ _ _ f Hd)=>Ht.
move: (@interp _ _ _ _ _ f Hd1)=>Ht1.
inv X. 
apply:p_pair. apply:Ht. apply:X0. apply:Ht1. apply:X1.

inv X. con. apply:X0. apply:f. apply:i. apply:X1.

move: (proj_fix D)=>Hd.

eapply interp. 2: apply:Hd.
intros.
rewrite !inE in H. destruct (eqVneq (x,y) (r0,r1)). inv e. ssa. 
(*      clear e H p. *) (*move: (interp _ _ _ p0)=>Hl. *)
clear D H e.
move: r0 r1 X0 d Hd.
fix IH 3.
move=> r0 r1. case; intros. 
      
inversion p0;subst;eauto.
      elim.
      apply:Hl
      simpl in H. apply:f. eauto. apply:X.
apply:interp. apply:p0.






intros. 

move: (@interp _ _ _ _ d f Hd).

apply:interp. apply:f. 
Check D_dom_plus.
apply Hd.


move: (@interp _ _ _ _ _ _ Hd).

refine (



(*Definition interp_base d := 
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
end.*)




(*Definition dsl_inj : forall d d0 d1 (f : dsl -> dsl), d = d0 -> d = d1 -> f d0 = f d1 :=
fun d d0 d1 f H H0 => (f_equal f (Logic.eq_trans (Logic.eq_sym H) H0)).

*)

(*Definition trans0_type l r r' (d : dsl l r r') :=  match d with | ctrans r0 r1 r2 _ _ => dsl l r0 r1 | _ => dsl l r r' end.

Definition trans0_inj l r r' := (fun d : (dsl l r r') => match d in dsl _ r r' return trans0_type d with
                                                      | ctrans _ _ _ d0 d1 => d0
                                                      | d' => d'
                                                      end). *)


(*C
Definition existT_inj (A : Type) (P : A -> Prop) (H:{ x : A | P x}) := 
match H with 
| existT _ _ x H' =>*)
(*Print dsl.
Check dsl_fix.
Fixpoint dec_eqc l r0 r1 (d0 d1: dsl l r0 r1) := 
match d0,d1 with 
| shuffle _ _ _,shuffle _ _ _ => true 
| shuffleinv _ _ _,shuffleinv _ _ _ => true 
| retag _ _,retag _ _ => true 

| untagL _ ,untagL _  => true 

| untagLinv _,untagLinv _ => true

| untag _,untag  _ => true 

| tagL _ _,tagL _ _ => true 

| assoc _ _ _,assoc _ _ _ => true 

| associnv _ _ _,associnv _ _ _ => true 

| swap _,swap _ => true 

| swapinv _,swapinv  _ => true

| proj _, proj _ => true 

| projinv _,projinv _ => true 

| abortR _,abortR _ => true 

| abortRinv _,abortRinv _ => true 

| abortL _,abortL _ => true 
  
| distL _ _ _,distL _ _ _ => true 

| distLinv _ _ _,distLinv _ _ _ => true 
| distR _ _ _,distR _ _ _ => true 

| distRinv _ _ _,distRinv _ _ _ => true 

| wrap _,wrap _ => true 

| wrapinv _,wrapinv _ => true 

| drop _,drop _ => true 

| dropinv _,dropinv _ => true 

| cid _,cid _ => true 

| ctrans _ _ _ p0 p1,ctrans _ _ _ p0' p1' => true  (*fix*)

| cplus _ _ _ _ p0 p1 ,cplus _ _ _ _ p0' p1'  => true  (*fix*)


| cseq _ _ _ _ p0 p1,cseq _ _ _ _ p0' p1' => true 

| cstar _ _ p0,cstar  _ _ p0' => true (*fix*)

| dsl_var _ _ _ Hin, dsl_var _ _ _ Hin' => true 

| dsl_fix _ _ p0, dsl_fix _ _ p1' => true
| _,_=> false 
end.



Lemma eq_test : forall (l l' : seq (regex * regex)) x (H H': x \in l), H = H'.
Proof.
intros. rewrite H.
Set Printing All. rewrite H.*)



(*Lemma dep_f_equal
     : forall l r r'  (d d' : dsl l r r'), d = d' -> False.
Proof.
intros.
Check (trans0_inj d).
have: trans0_type d = trans0_type d'. subst. done.
move=> Heq.
Check eq_rect.
Check (@eq_rect (dsl l r r') d (fun x => trans0_type x) (trans0_inj d) d' H). (fun x => d : X)



Check (trans0_inj d').
have: trans0_inj d : trans0_type d'.
Check eq_rect.


Check *)

(*Lemma ctrans_inj : forall l r0 r1 r2 (x p:dsl l r0 r1) (y p':dsl l r1 r2),
ctrans x y = ctrans p p' -> x = p.
Proof.
intros. clear eqs_aux eqs2.
Check f_equal.
Check  (@trans0_inj l r0 r1).
Check f_equal.
Print f_equal.
Check (f_equal _(trans0_inj l r0 r1).
Check (match ctrans x y with 
         | ctrans _ _ => x 
Check f_equal.

 Set Printing All.
case: H.*)

Definition proj_sig {A : Type} {P : A -> Type}  (H : { x &  P x}) : A :=
match H with 
| existT x _ => x
end.

Definition proj_sig2 {A : Type} {P : A -> Type}  (H : { x &  P x}) : P (proj_sig H) :=
match H with 
| existT _ H => H
end.

(*Definition proj_sig2 {A : Type} {P : A -> Prop}  (H : { x| P x}) : A :=
match H with 
| exist x _ => x
end.*)





(*end.
match r as r' return pTree r' -> nat  with 
| Eps => fun _ => 1
| Empt => fun _ => match p with | p_tt  => _ | _ => _ end
| Event a => fun _ => 0
| Plus r0 r1 => fun p => match p with | p_inl r0 _ p0 => (pTree_0size r0 p0).+1
                                  | p_inr _ r1 p1 => (pTree_0size r1 p1).+1
                                                                     
                      end 
| Seq r0 r1 => fun p => match p with | p_pair _ _ p0 p1 => ((pTree_0size r0 p0) + (pTree_0size r1 p1)).+1
                    end
| Star r0 => fun p => match p with 
                  | p_fold r0  p0 => pTree_0size (Eps _+_ r0 _;_ (Star r0)) p0
                   end 
end) p.

Fixpoint pTree_0size r  (p : pTree r) := 
(match r as r' return pTree r' -> nat  with 
| Eps => fun _ => 1
| Empt => fun _ => match p with | p_tt  => _ | _ => _ end
| Event a => fun _ => 0
| Plus r0 r1 => fun p => match p with | p_inl r0 _ p0 => (pTree_0size r0 p0).+1
                                  | p_inr _ r1 p1 => (pTree_0size r1 p1).+1
                                                                     
                      end 
| Seq r0 r1 => fun p => match p with | p_pair _ _ p0 p1 => ((pTree_0size r0 p0) + (pTree_0size r1 p1)).+1
                    end
| Star r0 => fun p => match p with 
                  | p_fold r0  p0 => pTree_0size (Eps _+_ r0 _;_ (Star r0)) p0
                   end 
end) p.

| p_tt =>  1 
| p_bot => 1 
| p_singl _ => 1
| p_inl _ _ p0 => (pTree_0size p0).+1
| p_inr _ _ p0 => (pTree_0size p0).+1
| p_pair _ _ p0 p1=> ((pTree_0size p0) + (pTree_0size p1)).+1
| p_fold _ p0 => (pTree_0size p0).+1
end.*)



Definition distL_i A' B C : (A' _;_ (B _+_ C)) <T= ((A' _;_ B) _+_ (A' _;_ C)). 
ipt.
Defined.


(*Lemma non_expansive_test : forall A B C (T : pTree (A _;_ (B _+_ C))), pTree_1size (distL_i T) <= pTree_1size T.
Proof.
intros.
move: T. 
 rewrite /distL_i. destruct T.*)

(*Definition proj_trans0 : (r0 r1 r2 : regex) (p0: dsl l r0 r1) (p1: dsl l r1 r2) (p : ctrans p0 p1) := *)

(*Lemma testtest (a : regex) : a == a.
Proof.
rewrite eqE.

have:  (Equality.class_of syntax_regex__canonical__eqtype_Equality) =  (Equality.class_of syntax_regex__canonical__eqtype_Equality).
simpl.
simpl. rewrite /hasDecEq.eq_op.
simpl.
*)

Definition proj_trans0 n l (r0 r r1: regex) (p0: dsl l r0 r) (p1: dsl l r r1)  
           (D : D_dom n (ctrans p0 p1)) : D_dom n p0.
inv D.
do ? apply dsl_proj2 in H0. subst. done.
Defined.

(*
(*rewrite sigT in*)
refine(
match D in D_dom _ p' return p' = ctrans p0 p1 -> D_dom n p0 with 
| D_trans _ x y Dx Dy => _
| _ => _
end Logic.eq_refl).  done.
intros.  inv H.
do ? apply dsl_proj2 in H2. subst. done.
Defined.*)

Definition proj_trans1 n l (r0 r r1: regex) (p0: dsl l r0 r) (p1: dsl l r r1)  
           (D : D_dom n (ctrans p0 p1)) : D_dom n p1.
inv D.
do ? apply dsl_proj2 in H4. subst. done.
Defined.

Definition proj_plus0 n l (r0 r1 r0' r1': regex) (p0: dsl l r0 r1) (p1: dsl l r0' r1')  
           (D : D_dom n (cplus p0 p1)) : D_dom n p0.
inv D.
do ? apply dsl_proj2 in H4. subst. done.
Defined.


Definition proj_plus1 n l (r0 r1 r0' r1': regex) (p0: dsl l r0 r1) (p1: dsl l r0' r1')  
           (D : D_dom n (cplus p0 p1)) : D_dom n p1.
inv D.
do ? apply dsl_proj2 in H5. subst. done.
Defined.

Definition proj_seq0 n l (r0 r1 r0' r1': regex) (p0: dsl l r0 r1) (p1: dsl l r0' r1')  
           (D : D_dom n (cseq p0 p1)) : D_dom n p0.
inv D.
do ? apply dsl_proj2 in H4. subst. done.
Defined.


Definition proj_seq1 n l (r0 r1 r0' r1': regex) (p0: dsl l r0 r1) (p1: dsl l r0' r1')  
           (D : D_dom n (cseq p0 p1)) : D_dom n p1.
inv D.
do ? apply dsl_proj2 in H5. subst. done.
Defined.


(**(*rewrite sigT in*)
refine(
match D in D_dom _ p' return p' = ctrans p0 p1 -> D_dom n p1 with 
| D_trans _ x y Dx Dy => _
| _ => _
end Logic.eq_refl).  done.
intros.  inv H.
do ? apply dsl_proj2 in H3. subst. done.
Defined.*)


(*Definition proj_trans0  d d0 d1 n  (D : D_dom d n) :  full_unf d = ctrans d0 d1 -> D_dom d0 n.
refine(
match D with
| D_trans d' d0' d1' n' Heq Hd Hd' => fun HQ => (eq_rect d0' (fun x => D_dom x n') Hd _ ((dsl_inj trans0_inj Heq HQ)))
| _ => fun HQ => _
end).


Defined.*)

(*Fixpoint interp l r0 r1 (p : dsl l r0 r1) (f : forall x y, (x,y) \in l -> (pTree x -> pTree y))
 {struct p}:
   pTree r0 -> pTree r1.
case: p;intros;try solve [clear f; ipt | clear f;pt].

eapply interp. apply:d0. apply:f. 
eapply interp. apply:d. apply:f. apply:X. 

inv X. apply:p_inl. eapply interp. apply:d. apply:f. apply:X0.
apply:p_inr. eapply interp. apply:d0. apply f. apply:X0.

inv X. con. eapply interp. apply d. apply f. apply X0.
eapply interp. apply d0. apply f. apply X1. 

inv X. con. apply X0. eapply f. apply i. apply X1.

eapply interp. apply:d. intros. rewrite !inE in H. 

de (orP H).
move: (proj_trans0 D)=>Hd.
move: (proj_trans1 D)=>Hd1.
eapply interp. apply:f. apply:Hd1. 
eapply interp. apply:f. apply:Hd. apply:X.

move: (proj_plus0 D)=>Hd.
move: (proj_plus1 D)=>Hd1.
move: (@interp _ _ _ _ _ f Hd)=>Ht.
move: (@interp _ _ _ _ _ f Hd1)=>Ht1.
inv X. 
apply:p_inl. apply:Ht. apply:X0.
apply:p_inr. apply:Ht1. apply:X0.

move: (proj_seq0 D)=>Hd.
move: (proj_seq1 D)=>Hd1.
move: (@interp _ _ _ _ _ f Hd)=>Ht.
move: (@interp _ _ _ _ _ f Hd1)=>Ht1.
inv X. 
apply:p_pair. apply:Ht. apply:X0. apply:Ht1. apply:X1.

inv X. con. apply:X0. apply:f. apply:i. apply:X1.*)


Fixpoint interp l r0 r1 (p : dsl l r0 r1) (f : forall x y, (x,y) \in l -> (pTree x -> pTree y)) {struct p}
 :
   pTree r0 -> pTree r1.
(*case: p D;intros;try solve [clear f; ipt | clear f;pt].*)

refine (
match p in dsl _ x y return r0 = x -> r1 = y ->pTree x-> pTree y  with 
| dsl_fix r0 r1 p0 => _
| _ => _ 
end Logic.eq_refl Logic.eq_refl).
(*all:intros;subst.
all:try solve .

clear f. pt.
 Print pTree. apply:p_inr. done.

all:eauto.
Qed.*)
31: { intros. inv X. con. done. apply:f. eauto. done. } 
31: { intros. subst. 
move: X. fix IH 1.
(* eapply interp. 2:eauto. 2:eauto. eauto. } *)

move: X.
move: (@interp _ _ _ p0).

eapply interp. apply p0.
clear X.
intros.
rewrite !inE in H. destruct (eqVneq (x,y) (r0,r1)). inv e. ssa. 
clear e H p.
move: r0 r1 X p0.
fix IH 3.
move=> r0 r1. case; intros. 
      
inversion p0;subst;eauto.
      elim.
      apply:Hl
      simpl in H. apply:f. eauto. apply:X.
apply:interp. apply:p0.







Check D_dom.
Check D_fix.
(*| D_base d n f :  interp_base (full_unf d) = Some f ->  D_dom d n*)
| D_trans d d0 d1 n : (*full_unf d = ctrans d0 d1 -> *)
                    D_dom d0 n -> D_dom d1 n ->  D_dom d n
(*| D_trans d d0 d1 T : full_unf d = ctrans d0 d1 -> 
                    D_dom d0  T -> (forall T',  D_dom d1 T') -> D_dom d T*)
| D_plus d d0 d1 n : full_unf d = (cplus d0 d1) ->  D_dom d0 n -> D_dom d1 n  -> D_dom d n
| D_seq d d0 d1 n  : full_unf d = (cseq d0 d1) ->  D_dom d0 n -> D_dom d1 n  -> D_dom d n
| D_star d d0 n : full_unf d = cstar d0 -> D_dom d0 n -> D_dom d n
| D_guard d d0 n n' : full_unf d =  guard d0 -> n = n'.+1 ->   D_dom d0 n' -> D_dom d n
| D_stop d d0 n : full_unf d = guard d0 -> n = 0  -> D_dom d n.
Hint Constructors D_dom.




Inductive D_dom : dsl -> nat -> Prop := 
| D_base d n f :  interp_base (full_unf d) = Some f ->  D_dom d n
| D_trans d d0 d1 n : full_unf d = ctrans d0 d1 -> 
                    D_dom d0 n -> D_dom d1 n ->  D_dom d n
(*| D_trans d d0 d1 T : full_unf d = ctrans d0 d1 -> 
                    D_dom d0  T -> (forall T',  D_dom d1 T') -> D_dom d T*)
| D_plus d d0 d1 n : full_unf d = (cplus d0 d1) ->  D_dom d0 n -> D_dom d1 n  -> D_dom d n
| D_seq d d0 d1 n  : full_unf d = (cseq d0 d1) ->  D_dom d0 n -> D_dom d1 n  -> D_dom d n
| D_star d d0 n : full_unf d = cstar d0 -> D_dom d0 n -> D_dom d n
| D_guard d d0 n n' : full_unf d =  guard d0 -> n = n'.+1 ->   D_dom d0 n' -> D_dom d n
| D_stop d d0 n : full_unf d = guard d0 -> n = 0  -> D_dom d n.
Hint Constructors D_dom.



Check dsl_fix.



(*Only return None when computation fuel runs out*)
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
                 | _ => Some up_bot
                end
| cseq  d0 d1  => fun HQ T=> 
                   match T with 
                   | up_pair T0 T1 => if (@interp _ d0 (proj_seq0 HQ D) T0) is Some T0'
                                     then if @interp _ d1 (proj_seq1 HQ D) T1 is Some T1'
                                                     then (Some (up_pair T0' T1'))
                                                     else None (*propegate missing fuel error as None rather than Some up_bot for typing error*)
                                     else None
                   | _ => Some up_bot (*error due to typing so return Some up_bot*)
                 end
| cstar d0 => fun HQ T => (fix cstar_i T' {struct T'} := 
                   match T' with 
                      | up_fold T0 => match T0 with 
                                     | up_inl up_tt => Some (up_fold (up_inl up_tt))
                                     | up_inr (up_pair T1 T2) => if (@interp _ d0 (proj_star HQ D) T1, cstar_i T2) 
                                                                     is (Some T',Some T'') then
                                                                  Some ( up_fold (up_inr (up_pair T' T''))) else None
                                     | _ => Some up_bot
                                     end
                      | _ => Some up_bot
                      end) T
| guard  d0 => fun HQ T => match T with (*Prioritize returning Some up_bot over non when fuel is lacking*)
                       | up_pair (up_singl a) T0 =>
                           match n as n0 return n = n0 -> option upTree with 
                           | n'.+1 => fun Hn => if @interp _ d0 (proj_guard HQ Hn D) T0 is Some T' 
                                                    then Some (up_pair (up_singl a) T') 
                                                    else None                                         
                           | _ => fun _ => None
                           end Logic.eq_refl                                                                            
                       | _ => Some up_bot
                       end                         
| _ => fun HQ T => if interp_base (full_unf d) is Some f then Some (f T) else None
end Logic.eq_refl.

(*Locked version to not expand definition*)
Definition interpl {n} d (D : D_dom d n) T  : option upTree := 
locked (@interp n d D T).







(*


Lemma nat_mem : 0 \in 0::nil.
Proof.
rewrite inE eqxx //.
Defined.

Eval hnf in nat_mem.



CoInductive dsl_co : regex -> regex -> Type := 
| Co_build A B : (dsl dsl_co) A B -> dsl_co A B.
(*Arguments Co_build {A B}.*)

*)















(*(A' _+_ B) _+_ C <T= A' _+_ (B _+_ C).*)
Notation "c0 <T= c1" := ((pTree c0) -> (pTree c1))(at level 63).

(*Definition untag_i A' : A' _+_ A' <T= A'.
intro. inv X. 
Defined.*)
(*Defined.
refine(
fun T =>
match T in pTree c0 return c0 = A' _+_ A' -> pTree A' with 
| p_inl _ _ T' => fun HQ => _
| p_inr _ _ T' => fun HQ => _
| _ => _
end Logic.eq_refl)
. done. done. case: HQ. intros. subst. apply:T'. case:HQ. intros. subst. apply:T'.
done. done.
Defined.*)


Definition shuffle_i A' B C  : (A' _+_ B) _+_ C <T= A' _+_ (B _+_ C). 
ipt.
Defined.
(*:=
fun  T => 
match T with
| p_inl _ _ (p_inl _ _ T') => (p_inl T')
| p_inl _ _(p_inr _ _ T') =>  (p_inr (p_inl T'))
| p_inr _ _ T' => (p_inr _ _ (p_inr _ _ T'))
end.*)

Definition shuffleinv_i A' B C :  A' _+_ (B _+_ C)  <T= (A' _+_ B) _+_ C.
ipt.
Defined.
(*fun  T => 
match T with 
| up_inl T' => up_inl (up_inl T')
| p_inr (up_inl T') => up_inl (p_inr T')
| p_inr (p_inr T') => (p_inr T')
end.*)

Definition retag_i A' B  : A' _+_ B <T= B _+_ A'.
ipt.
Defined.
(*fun T => 
match T with 
| p_inl T' => p_inr T' 
| p_inr T' => p_inl T'
end. *)

Definition untagL_i A' : Empt _+_ A' <T= A'. 
ipt.
Defined.
(*:=
fun T => 
match T with 
| p_inl T' => match T' with end 
| p_inr T' => T' 
end.*)

Definition untagLinv_i {A} : A <T= Empt _+_ A :=
fun T => p_inr T.

Definition untag_i A' : A' _+_ A' <T= A'. 
ipt. 
Defined.
(*:=
fun T =>
match T with 
| p_inl T' => T'
| p_inr T' => T'
end.*)

Definition tagL_i {A B} :  A <T= (A _+_ B ) := p_inl.

Definition assoc_i A' B C : ((A' _;_ B) _;_ C)<T=  (A' _;_ (B _;_ C)).
ipt. 
Defined.
(*:= 
fun T => let: ((T0,T1),T2) := T in (T0,(T1,T2)).*)

Definition associnv_i A' B C : (A' _;_ (B _;_ C)) <T=  ((A' _;_ B) _;_ C).
ipt.
Defined.
(*fun T => let: (T0,(T1,T2)) := T in ((T0,T1),T2).*)

Definition swap_i A' :  (A' _;_ Eps)<T=  (Eps _;_ A').  
ipt.
Defined.
(*:= fun T => (tt,T.1).*)
Definition swapinv_i A' : (Eps _;_ A') <T= (A' _;_ Eps).
ipt.
Defined.
(* := fun T => (T.2,tt).*)

Definition proj_i A' : (Eps _;_ A')<T=  A'.  
ipt.
Defined.
(*:= snd.*)
Definition projinv_i {A'} : A' <T= (Eps _;_ A'). 
ipt. con. con. done.
Defined.
(*:= fun T => (tt,T).*)

Definition abortR_i A' : (A' _;_ Empt) <T=  Empt. 
ipt. 
Defined.
(*:= fun T => match T.2 with end.*)
Definition abortRinv_i A' : Empt  <T=  (A' _;_ Empt). 
ipt.
Defined.
(*:= fun T => match T with end.*)

Definition abortL_i A' : (Empt _;_ A') <T=  Empt. 
ipt.
Defined.
(*:= fun T => match T.1 with end.*)

Definition abortLinv_i A' : Empt <T=   (Empt _;_ A'). 
ipt.
Defined.
(*:= fun T => match T with end.*)

Definition distL_i A' B C : (A' _;_ (B _+_ C)) <T= ((A' _;_ B) _+_ (A' _;_ C)). 
ipt.
Defined.
(*:= 
fun T => let: (T0,T1) := T in 
match T1 with 
| p_inl T' => p_inl (T0,T')
| p_inr T' => p_inr (T0,T')
end.*)
Definition distLinv_i A' B C :  ((A' _;_ B) _+_ (A' _;_ C)) <T= (A' _;_ (B _+_ C)). 
ipt.
Defined.
(*:=
fun T => 
match T with 
| p_inl (T0,T1) => (T0,p_inl T1)
| p_inr (T0,T1) => (T0,p_inr T1)
end.*)

Definition distR_i A' B C : ((A' _+_ B) _;_ C) <T=  ((A' _;_ C) _+_ (B _;_ C)). 
ipt.
Defined.
(*:=
fun T => let: (T0,T1) := T in 
match T0 with 
| p_inl T' => p_inl (T',T1)
| p_inr T' => p_inr (T',T1)
end.*)
Definition distRinv_i A' B C : ((A' _;_ C) _+_ (B _;_ C))  <T= ((A' _+_ B) _;_ C). 
ipt.
Defined.
(*:=
fun T => 
match T with 
| p_inl (T0,T1) => (p_inl T0,T1)
| p_inr (T0,T1) => (p_inr T0,T1)
end.*)

Definition wrap_i A' : (Eps _+_ (A' _;_ Star A')) <T= (Star A') := p_fold.
(*fun T => 
match T with
| p_inl _ => nil 
| p_inr (T0,T1) => cons T0 T1
end.*)
Print pTree.
Definition wrapinv_i A' : (Star A') <T= (Eps _+_ (A' _;_ Star A')).
intro. inv X.
Defined.
(*fun T => 
match T with 
| nil => p_inl tt
| cons a T' => p_inr (a,T')
end.*)
Check p_fold.
Fixpoint pTree_0size r  (p : pTree r) := 
(match r as r' return pTree r' -> nat  with 
| Eps => fun _ => 1
| Empt => fun _ => match p with | p_tt  => _ | _ => _ end
| Event a => fun _ => 0
| Plus r0 r1 => fun p => match p with | p_inl r0 _ p0 => (pTree_0size r0 p0).+1
                                  | p_inr _ r1 p1 => (pTree_0size r1 p1).+1
                                                                     
                      end 
| Seq r0 r1 => fun p => match p with | p_pair _ _ p0 p1 => ((pTree_0size r0 p0) + (pTree_0size r1 p1)).+1
                    end
| Star r0 => fun p => match p with 
                  | p_fold r0  p0 => pTree_0size (Eps _+_ r0 _;_ (Star r0)) p0
                   end 
end) p.

| p_tt =>  1 
| p_bot => 1 
| p_singl _ => 1
| p_inl _ _ p0 => (pTree_0size p0).+1
| p_inr _ _ p0 => (pTree_0size p0).+1
| p_pair _ _ p0 p1=> ((pTree_0size p0) + (pTree_0size p1)).+1
| p_fold _ p0 => (pTree_0size p0).+1
end.
Definition drop_i A' :  (Star (Eps _+_ A')) <T= (Star A'). 
intro.
move: 
:=
fix drop_i T := 
match unfold_s T with
| p_inl _ => fold_s (p_inl tt)
| p_inr (a,T') => match a with | p_inl tt => fold_s (p_inl tt) | p_inr a' => fold_s (p_inr (a',drop_i T')) end
end.

Definition dropinv_i A' : (Star A) <T= (Star (Eps _+_ A)) :=
fix dropinv_i T := 
match unfold_s T with 
| p_inl _ => fold_s (p_inl tt)
| p_inr (a,T') => fold_s (p_inr (p_inr a,dropinv_i T'))
end.

Definition cid_i {c} : c <T= c := fun x => x.


Definition cseq_i A' A' B B'  (f0 : A' <T=  A) (f1 : B <T= B') : (A' _;_ B) <T= (A' _;_ B') :=
fun T => let: (T0,T1) := T in (f0 T0, f1 T1).

Definition cstar_i A' B (f : A' <T= B) : (Star A)  <T= (Star B) := 
fix cstar_i T := 
match unfold_s T with 
| p_inl _ => fold_s (p_inl tt)
| p_inr (a,T') => fold_s (p_inr (f a,(cstar_i T')))
end.

Definition ctrans_i A' B C (f : A' <T=B) (f' :B <T=C) :  A' <T=C :=
f' \o f.

Definition cplus_i A' B A' B' (f :  A' <T=A' ) (f' :  B <T=B' ) : A' _+_ B <T=A' _+_ B' :=
fun T => 
match T with 
| p_inl T' => p_inl (f T')
| p_inr T' => p_inr (f' T')
end.




Definition shuffle_o A' B C : (A' _+_ B) _+_ C <O= A' _+_ (B _+_ C) := Some \o shuffle_i.  
Definition shuffleinv_o A' B C :  A' _+_ (B _+_ C)  <O= (A' _+_ B) _+_ C := Some \o shuffleinv_i.

Definition retag_o A' B : A' _+_ B <O= B _+_ A' := Some \o retag_i.

Definition untagL_o A' : Empt _+_ A' <O= A' := Some \o untagL_i.
Definition untagLinv_o A' : A' <O= Empt _+_ A' := Some \o untagLinv_i.

Definition untag_o A' : A' _+_ A' <O= A' := Some \o untag_i.

Definition tagL_o A' B :  A' <O= (A' _+_ B ) := Some \o tagL_i.

Definition assoc_o A' B C : ((A' _;_ B) _;_ C)<O=  (A' _;_ (B _;_ C)) := Some \o assoc_i.
Definition associnv_o A' B C : (A' _;_ (B _;_ C)) <O=  ((A' _;_ B) _;_ C) := Some \o associnv_i.

Definition swap_o A' :  (A' _;_ Eps)<O=  (Eps _;_ A) := Some \o swap_i.
Definition swapinv_o A' : (Eps _;_ A) <O= (A' _;_ Eps) := Some \o swapinv_i.

Definition proj_o A' : (Eps _;_ A)<O=  A' := Some \o proj_i.
Definition projinv_o A' : A' <O= (Eps _;_ A) := Some \o projinv_i.

Definition abortR_o A' : (A' _;_ Empt) <O=  Empt := fun T => match T.2 with end.
Definition abortRinv_o A' : Empt  <O=  (A' _;_ Empt) := fun T => match T with end.

Definition abortL_o A' : (Empt _;_ A) <O=  Empt := fun T => match T.1 with end.
Definition abortLinv_o A' : Empt <O=   (Empt _;_ A) := fun T => match T with end.

Definition distL_o A' B C : (A' _;_ (B _+_ C)) <O= ((A' _;_ B) _+_ (A' _;_ C)) := Some \o distL_i.
Definition distLinv_o A' B C :  ((A' _;_ B) _+_ (A' _;_ C)) <O= (A' _;_ (B _+_ C)) := Some \o distLinv_i.

Definition distR_o A' B C : ((A' _+_ B) _;_ C) <O=  ((A' _;_ C) _+_ (B _;_ C)) := Some \o distR_i.
Definition distRinv_o A' B C : ((A' _;_ C) _+_ (B _;_ C))  <O= ((A' _+_ B) _;_ C) := Some \o distRinv_i.

Definition wrap_o A' : (Eps _+_ (A' _;_ Star A)) <O= (Star A) := Some \o wrap_i.
Definition wrapinv_o A' : (Star A) <O= (Eps _+_ (A' _;_ Star A)) := Some \o wrapinv_i.

Definition drop_o A' :  (Star (Eps _+_ A)) <O= (Star A) := Some \o drop_i.
Definition dropinv_o A' : (Star A) <O= (Star (Eps _+_ A)) := Some \o dropinv_i.

Definition cid_o {c} : c <O= c := fun x => Some x.

Definition cseq_o A' A' B B'  (f0 : A' <O=  A) (f1 : B <O= B') : (A' _;_ B) <O= (A' _;_ B') :=
fun T => let: (T0,T1) := T in if (f0 T0, f1 T1) is (Some T0',Some T1') then Some (T0',T1') else None.

Definition cstar_o A' B (f : A' <O= B) : (Star A)  <O= (Star B) := 
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
end.

Definition guard_o {a c0 c1} (f : c0 <O= c1) : ((Event a) _;_ c0) <O= ((Event a) _;_ c1) := 
fun T => let: (a,T') := T in if f T' is Some T'' then Some (a,T'') else None.



















match p0 with 
                                                   | Test_unfold y z p0' => proof_unfold (to_proof p0')
                                                                                       end
                         end
end.                                              
                          
end.
                          |
p_guard (proof_unfold (to_proof p0'))
                         end
|







~> pf (*assoc +*)



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
Definition flat_pred c0 f := forall s, typing s c0 -> uflatten (f s) = uflatten s.

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

Lemma shuffle_i_flat :  forall A B C, flat_pred ((A _+_ B) _+_ C) shuffle_i.
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

Lemma shuffleinv_i_flat : forall A B C,   flat_pred (A _+_ (B _+_ C))  shuffleinv_i.
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
Lemma retag_i_flat : forall A B,  flat_pred (A _+_ B) retag_i.
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
Lemma untagL_i_flat : forall A, flat_pred (Empt _+_ A) untagL_i.
Proof. lt. Qed.
(* A <T= Empt _+_ A*)
Definition untagLinv_i :  fType :=
fun T => up_inr T.
Lemma untagLinv_i_t : forall A,  A <T= Empt _+_ A ~> untagLinv_i.
Proof. lt. Qed.
Lemma untagLinv_i_flat : forall A,  flat_pred A untagLinv_i.
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

Lemma untag_i_flat : forall A, flat_pred (A _+_ A) untag_i.
Proof. lt. Qed.

(* A <T= (A _+_ B ) *)
Definition tagL_i : fType  := up_inl.
Lemma tagL_i_t : forall A B,  A <T= (A _+_ B ) ~>tagL_i.
Proof. lt. Qed.
Lemma tagL_i_flat : forall A,  flat_pred A tagL_i.
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
Lemma assoc_i_flat : forall A B C, flat_pred ((A _;_ B) _;_ C) assoc_i.
Proof. intros. intro. intro. inv H. simpl. inv H3. simpl. rewrite catA //.
Qed.

(*(A _;_ (B _;_ C)) <T=  ((A _;_ B) _;_ C)*)
Definition associnv_i : fType  :=
fun T => 
match T with 
| up_pair T0 (up_pair T1 T2) => up_pair (up_pair T0 T1) T2
| _ => up_bot
end.
Lemma associnv_i_t : forall A B C, (A _;_ (B _;_ C)) <T=  ((A _;_ B) _;_ C) ~> associnv_i.
Proof. lt. Qed.
Lemma associnv_i_flat : forall A B C, flat_pred (A _;_ (B _;_ C)) associnv_i.
Proof. intros. intro. intros. inv H. inv H4. inv H4. simpl. rewrite catA //.
Qed.

(* (A _;_ Eps)<T=  (Eps _;_ A) *)
Definition swap_i : fType := 
fun T => 
match T with 
| up_pair T0 up_tt => up_pair up_tt T0
| _ => up_bot 
end.
Lemma swap_i_t : forall A,  (A _;_ Eps)<T=  (Eps _;_ A) ~> swap_i.
Proof. lt. Qed.
Lemma swap_i_flat : forall A, flat_pred (A _;_ Eps) swap_i.
Proof. intros. intro. intros. inv H. inv H. inv H4. simpl. rewrite cats0 //.
Qed.

(* (Eps _;_ A) <T= (A _;_ Eps)*)
Definition swapinv_i : fType := 
fun T => 
match T with 
| up_pair up_tt T' => up_pair T' up_tt
| _ => up_bot
end.
Lemma swapinv_i_t : forall A, (Eps _;_ A) <T= (A _;_ Eps) ~> swapinv_i.
Proof. lt. Qed.
Lemma swapinv_i_flat : forall A, flat_pred (Eps _;_ A) swapinv_i.
Proof. intros. intro. intros. inv H. inv H. inv H3. simpl. rewrite cats0 //.
Qed.

(* (Eps _;_ A)<T=  A*)
Definition proj_i : fType := 
fun T => 
match T with 
| up_pair up_tt T' => T'
| _ => up_bot
end.
Lemma proj_i_t : forall A, (Eps _;_ A)<T=  A ~> proj_i.
Proof. lt. Qed.
Lemma proj_i_flat : forall A, flat_pred (Eps _;_ A) proj_i.
Proof. lt. Qed.

(* A <T= (Eps _;_ A)*)
Definition projinv_i : fType := 
fun T => up_pair up_tt T.
Lemma projinv_i_t : forall A,  A <T= (Eps _;_ A) ~> projinv_i.
Proof. lt. Qed.
Lemma projinv_i_flat : forall A,  flat_pred A projinv_i.
Proof. lt. Qed.

(*Does this make sense, the domain is empty*)
(* (A _;_ Empt) <T=  Empt*)
Definition abortR_i : fType := 
fun _ => up_bot.
Lemma abortR_i_t : forall A, (A _;_ Empt) <T=  Empt ~> abortR_i.
Proof. lt. Qed.
Lemma abortR_i_flat : forall A, flat_pred (A _;_ Empt) abortR_i.
Proof. lt. Qed.
(*match T with 
| up_pair T' up_bot => up_bot
| _ => up_bot
end. *)

(*Empt  <T=  (A _;_ Empt)*)
Definition abortRinv_i : fType  := fun _ => up_bot.
Lemma abortRinv_i_t : forall A, Empt  <T=  (A _;_ Empt) ~> abortRinv_i.
Proof. lt. Qed.
Lemma abortRinv_i_flat : flat_pred Empt abortRinv_i.
Proof. lt. Qed.
(*fun T => 
match T with end.*)

(* (Empt _;_ A) <T=  Empt*)
Definition abortL_i : fType := fun _ => up_bot.
Lemma abortL_i_t : forall A,  (Empt _;_ A) <T=  Empt ~> abortL_i.
Proof. lt. Qed.
Lemma abortL_i_flat : forall A, flat_pred (Empt _;_ A) abortL_i.
Proof. lt. Qed.
(*fun T => match T.1 with end.*)

(* Empt <T=   (Empt _;_ A) *)
Definition abortLinv_i : fType := fun _ => up_bot.
Lemma abortLinv_i_t : forall A, Empt <T=   (Empt _;_ A) ~>abortLinv_i.
Proof. lt. Qed.
Lemma abortLinv_i_flat :  flat_pred Empt abortLinv_i.
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
Lemma distL_i_flat : forall A B C, flat_pred (A _;_ (B _+_ C)) distL_i.
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
Lemma distLinv_i_flat : forall A B C, flat_pred ((A _;_ B) _+_ (A _;_ C)) distLinv_i.
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
Lemma distR_i_flat : forall A B C, flat_pred ((A _+_ B) _;_ C)distR_i.
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
Lemma distRinv_i_flat : forall A B C,  flat_pred ((A _;_ C) _+_ (B _;_ C)) distRinv_i.
Proof. lt. Qed.

(*(Eps _+_ (A _;_ Star A)) <T= (Star A)*)
Definition wrap_i : fType  := up_fold.
Lemma wrap_i_t : forall A,(Eps _+_ (A _;_ Star A)) <T= (Star A) ~>wrap_i.
Proof. lt. Qed.
Lemma wrap_i_flat : forall A, flat_pred (Eps _+_ (A _;_ Star A)) wrap_i.
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
Lemma wrapinv_i_flat : forall A, flat_pred (Star A) wrapinv_i.
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
move=> r T. move Heq: (upTree_0size T) => n. move: Heq. suff: upTree_0size T <= n -> typing T (Star (Eps _+_ r)) -> typing (drop_i T) (Star r).
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. inv H4. inv H3. apply/IH. ssa. done.
con. con. con. done. apply/IH. ssa. lia. done.
Qed.

Lemma drop_i_flat : forall A, flat_pred (Star (Eps _+_ A)) drop_i.
Proof.
move=> r T. 
move Heq: (upTree_0size T) => n. move: Heq.
wlog: n T / upTree_0size T <= n. move=> H Heq. apply:H. 2:eauto. lia. move=> + _.
elim: n T.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt.  
move=> u Hsize Ht. inv Ht. inv H1. inv H2. inv H2. inv H4. inv H3. simpl. apply:IH. ssa. ssa.
simpl. f_equal. ssa. apply:IH. lia. ssa.
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
move=> r T. move Heq: (upTree_0size T) => n. move: Heq. suff: upTree_0size T <= n ->typing T (Star r) -> typing (dropinv_i T) (Star (Eps _+_ r)).
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq r. elim=>//=.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt. lt. lt. 
move=> u Hsize r0 Ht.  inv Ht. inv H1. inv H2.  eauto. inv H2. con. con. con. con. done. apply/IH. ssa. lia. eauto.
Qed.

Lemma dropinv_i_flat : forall A, flat_pred (Star A)  dropinv_i.
Proof.
move=> r T. 
move Heq: (upTree_0size T) => n. move: Heq.
wlog: n T / upTree_0size T <= n. move=> H Heq. apply:H. 2:eauto. lia. move=> + _.
elim: n T.
case=>//=.
move=> n IH. case=>//=. lt. lt. lt. lt.  
move=> u Hsize Ht. inv Ht. inv H1. inv H2. inv H2. 
simpl. f_equal. ssa. apply:IH. lia. ssa.
Qed.
(*match unfold_s T with 
| up_inl _ => fold_s (up_inl tt)
| up_inr (a,T') => fold_s (up_inr (up_inr a,dropinv_i T'))
end.*)

(* A <T= A *)
Definition cid_i : fType := fun x => x.
Lemma cid_i_t : forall A, A <T= A ~>cid_i.
Proof. lt. Qed.
Lemma cid_i_flat : forall A, flat_pred A cid_i.
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
Lemma cseq_i_flat : forall A B f0 f1, flat_pred A f0 -> flat_pred B f1 -> flat_pred (A _;_ B) (cseq_i f0 f1).
Proof. intros. intro. intros. inv H1. simpl. f_equal; eauto.
Qed.

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
Lemma ctrans_i_flat : forall A B f f', flat_pred A f -> A <T= B ~> f ->  flat_pred B f' ->  flat_pred A (ctrans_i f f').
Proof. intros. intro. intros. rewrite /ctrans_i /=. rewrite H1 //. rewrite H//. apply:H0. done.
Qed.

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
Lemma cplus_i_flat : forall A  B f f', flat_pred A f -> flat_pred B f'  -> flat_pred (A _+_ B) (cplus_i f f').
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
Lemma guard_i_flat : forall a A B f, flat_pred A f  -> A <T= B ~>f -> flat_pred ((Event a) _;_ A) (guard_i f).
Proof. intros. intro. intros. inv H1. inv H5. simpl. f_equal. apply:H. done.
Qed.

Hint Resolve shuffle_i_t shuffleinv_i_t retag_i_t untagL_i_t untagLinv_i_t untag_i_t
             tagL_i_t assoc_i_t associnv_i_t swap_i_t swapinv_i_t proj_i_t projinv_i_t abortR_i_t
             abortRinv_i_t abortL_i_t abortLinv_i_t distL_i_t distLinv_i_t distR_i_t distRinv_i_t
             wrap_i_t wrapinv_i_t drop_i_t dropinv_i_t cid_i_t ctrans_i_t cplus_i_t cseq_i_t (*cstar_i_t*) guard_i_t.

Hint Resolve shuffle_i_flat shuffleinv_i_flat retag_i_flat untagL_i_flat untagLinv_i_flat untag_i_flat
             tagL_i_flat assoc_i_flat associnv_i_flat swap_i_flat swapinv_i_flat proj_i_flat projinv_i_flat abortR_i_flat
             abortRinv_i_flat abortL_i_flat abortLinv_i_flat distL_i_flat distLinv_i_flat distR_i_flat distRinv_i_flat
             wrap_i_flat wrapinv_i_flat drop_i_flat dropinv_i_flat cid_i_flat ctrans_i_flat cplus_i_flat cseq_i_flat (*cstar_i_flat*) guard_i_flat.

Ltac flat_tac :=
  first  [ erewrite shuffle_i_flat | 
                 erewrite shuffleinv_i_flat |
                 erewrite retag_i_flat  |
                 erewrite untagL_i_flat |
                 erewrite untagLinv_i_flat |
                 erewrite untag_i_flat |
                 erewrite tagL_i_flat  |
                 erewrite assoc_i_flat |
                 erewrite associnv_i_flat|
                 erewrite swap_i_flat |
                 erewrite swapinv_i_flat |
                 erewrite proj_i_flat |
                 erewrite projinv_i_flat |
                 erewrite abortR_i_flat |
                 erewrite abortRinv_i_flat |
                 erewrite abortL_i_flat |
                 erewrite abortLinv_i_flat |
                 erewrite distL_i_flat | 
                 erewrite distLinv_i_flat |
                 erewrite distR_i_flat |
                 erewrite distRinv_i_flat |
                 erewrite  wrap_i_flat |
                 erewrite wrapinv_i_flat |
                 erewrite drop_i_flat |
                 erewrite dropinv_i_flat |
                 erewrite cid_i_flat |
                 erewrite ctrans_i_flat |
                 erewrite cplus_i_flat |
                 erewrite cseq_i_flat | (*cstar_i_flat*) 
                 erewrite guard_i_flat ].


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

(*Definition is_base d := 
match d with 
| ctrans _ _ | cplus _ _ | cseq _ _ | cstar _ | guard _ | var_dsl _ => false | _ => true 
end.


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
end.*)





(*Definition dsl_inj : forall d d0 d1 (f : dsl -> dsl), d = d0 -> d = d1 -> f d0 = f d1 :=
fun d d0 d1 f H H0 => (f_equal f (Logic.eq_trans (Logic.eq_sym H) H0)).

Definition trans0_inj := (fun e : dsl => match e with
                            | ctrans d2 _ => d2
                            | _ => e
                             end). 

(*This proof is quite large but the bragga method did the same, lemma true_false in ns.v*)
Lemma None_Some : forall (A : Type) (a : A), None <> Some a.
Proof.
intros. intro. inversion H. 
Qed.
Check D_trans.
Definition proj_trans0  d d0 d1 n  (D : D_dom d n) :  full_unf d = ctrans d0 d1 -> D_dom d0 n.
refine(
match D with
| D_trans d' d0' d1' n' Heq Hd Hd' => fun HQ => (eq_rect d0' (fun x => D_dom x n') Hd _ ((dsl_inj trans0_inj Heq HQ)))
| _ => fun HQ => _
end).
- case: (None_Some (Logic.eq_trans (f_equal interp_base (Logic.eq_sym HQ)) e)).
(*- move:)=>/= HH.*)
(*exact: (eq_rect d0' (fun x => D_dom x n') Hd _ ((dsl_inj trans0_inj Heq HQ))).*)
move: ((Logic.eq_trans (Logic.eq_sym e) HQ)) =>HH. inversion HH.
move: ((Logic.eq_trans (Logic.eq_sym e) HQ))=>HH.  inversion HH.
move: ((Logic.eq_trans (Logic.eq_sym e) HQ))=>HH.  inversion HH.
move: ((Logic.eq_trans (Logic.eq_sym e) HQ))=>HH.  inversion HH.
move: ((Logic.eq_trans (Logic.eq_sym e) HQ))=>HH.  inversion HH.
Defined.*)
(*'
move/eqP. rewrite eqE /=.
Show Proof. Check (introT eqP).


=>/=.
exact: (eq_rect d3 (fun x => D_dom x n0) Hd _ ((dsl_inj trans0_inj Heq HQ))).

simpl.
 HH).

Check (@eq_rect _ d3 (fun x => D_dom x n0) Hd _ HH).
apply/Logic.eq_trans. apply: (f_equal interp_base (Logic.eq_sym HQ)). apply: e.
move: (Logic.eq_trans e (f_equal interp_base HQ)).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ in e; inv e.
rewrite Heq in HQ; inv HQ. 
Defined.*)

Definition proj_trans0  d d0 d1 n (Heq : full_unf d = ctrans d0 d1)  (D : D_dom d n)  : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = ctrans d0 d1 -> D_dom d0 n with 
| D_trans _ _ _ _ Heq Hd Hle => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_trans1  d d0 d1 n (Heq : full_unf d = ctrans d0 d1) (D : D_dom d n)  : D_dom d1 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = ctrans d0 d1 ->   D_dom d1 n  with 
| D_trans _ _ _ _ Heq Hd Hle => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ.  
Defined.

Definition proj_plus0  d d0 d1 n (Heq : full_unf d = cplus d0 d1) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cplus d0 d1 -> D_dom d0 n with 
| D_plus _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_plus1  d d0 d1 n (Heq : full_unf d = cplus d0 d1) (D : D_dom d n) : D_dom d1 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cplus d0 d1 -> D_dom d1 n with 
| D_plus _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_seq0  d d0 d1 n (Heq : full_unf d = cseq d0 d1) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cseq d0 d1 -> D_dom d0 n with 
| D_seq _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_seq1  d d0 d1 n (Heq : full_unf d = cseq d0 d1) (D : D_dom d n) : D_dom d1 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cseq d0 d1 -> D_dom d1 n with 
| D_seq _ _ _ _ Heq Hd Hd' => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. 
Defined.

Definition proj_star  d d0 n (Heq : full_unf d = cstar d0) (D : D_dom d n) : D_dom d0 n.
Proof. refine(
match D in D_dom d' n return full_unf d' = cstar d0 -> D_dom d0 n with 
| D_star _ _ _ Heq Hd => fun HQ => _
| _ => fun HQ => _
end Heq).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. 
Defined.


Definition proj_guard  d d0 n n' (Heq : full_unf d = guard d0) (Hn : n = n'.+1) (D : D_dom d n) : D_dom d0 n'.
Proof. refine(
match D in D_dom d' n return full_unf d' = guard d0 -> n = n'.+1 -> D_dom d0 n' with 
| D_guard _ _ _ _ Heq Hneq Hd => fun HQ Hn => _
| _ => fun HQ Hn => _
end Heq Hn).
all: try solve [rewrite e in HQ; inv HQ].
rewrite HQ //in e. 
rewrite Heq in HQ; inv HQ. inv Hn. 
Defined.



Fixpoint event_size p := 
match p with 
| up_tt =>  0
| up_bot => 0
| up_singl _ => 1
| up_inl p0 => (event_size p0)
| up_inr p0 => (event_size p0)
| up_pair p0 p1=> ((event_size p0) + (event_size p1))
| up_fold p0 => (event_size p0)
end.

Lemma interp_trans_eq_some : forall n d0 d1 d Heq T T' (D0: D_dom d0 n) (D1 : D_dom d1 n), interpl D0 T = Some T'  -> 
interpl (D_trans d Heq D0 D1) T = interpl  D1 T'.
Proof.
intros. unlock interpl. simpl. erewrite Heq. simpl.  unlock interpl in H. rewrite H.  done.
Qed.

Lemma interp_trans_eq_none : forall n d0 d1 d Heq T (D0: D_dom d0 n) (D1 : D_dom d1 n), interpl D0 T = None  -> 
interpl (D_trans d Heq D0 D1) T = None.
Proof.
intros.  unlock interpl. simpl. erewrite Heq. unlock interpl in H. rewrite H.  done.
Qed.

(*Lemma interp_trans_eq_none : forall n d0 d1 d Heq T (D0: D_dom d0 n) (D1 : D_dom d1 n), interp D0 T = None  -> 
interp (D_trans d Heq D0 D1) T = None.
Proof.
intros. simpl. erewrite Heq. simpl. rewrite H.  done.
Qed.*)

Lemma interp_base_eq : forall d f n T (Heq : interp_base (full_unf d) = Some f), interpl (D_base d n Heq) T = Some (f T).
Proof. intros. unlock interpl.
simpl. destruct (full_unf d) eqn:Heqn. 
all: try solve [rewrite Heq //| ssa].
Qed.

Lemma interp_base_size : forall d f T, interp_base d = Some f -> event_size (f T) <= event_size T.
Proof.
case=>//=;intros.
all: try solve [inv H; case: T;ssa; case: u;ssa].
inv H. case: T;ssa. case: u;ssa. lia.
inv H. case: T;ssa. case: u0;ssa. lia.
inv H. case: T;ssa. case: u0;ssa. lia.
inv H. case: T;ssa. case: u;ssa. lia.
inv H. case: T;ssa. case: u0;ssa. 
inv H. clear H.

move Heq: (upTree_0size T) => n. move: Heq. suff: upTree_0size T <= n -> event_size (drop_i T) <= event_size T.
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq. elim=>//=.
case=>//=.
move=> n IH. case=>//=. case=>//=. case=>//=. case=>//=. case=>//=.
case=>//=. intros.  rewrite add0n. apply/IH.  lia.
intros. suff: event_size (drop_i u0) <= event_size u0. lia.
apply/IH. lia.

inv H. clear H.
move Heq: (upTree_0size T) => n. move: Heq. suff: upTree_0size T <= n -> event_size (dropinv_i T) <= event_size T.
move=>HH H2. apply/HH. subst. lia.
move=> Heq.
move: n T Heq. elim=>//=.
case=>//=.
move=> n IH. case=>//=. case=>//=. case=>//=. case=>//=. 
intros. suff: event_size (dropinv_i u0) <= event_size u0. lia.
apply/IH. lia.
Qed.

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
  | ip_guard p pf : full_unf pf = guard p -> R p -> invPred_gen R pf.
Hint Constructors invPred_gen.

Lemma invPred_gen_mon : monotone1 invPred_gen.
Proof.
move=> x r r'. elim=>//;eauto.
Qed.
Hint Resolve invPred_gen_mon : paco.

Definition invPred g := paco1  invPred_gen bot1 g.

(*Lemma invPred_unf : forall R p, invPred_gen R (full_unf p) -> invPred_gen R p.
Proof.
move=> R p. move Heq: (full_unf _)=>ef Hinv.
elim: Hinv Heq.
- move=> pf Heq0 Heq1. subst.*) 

Lemma to_invPred : forall r0 r1 p, r0 <C= r1 ~> p -> invPred p.
Proof.
pcofix CIH. move => r0 r1 p. sunfold. elim=>//.
all: try solve[intros; subst; pfold; con; rewrite H //;eauto].
- move=> c0 c1 c2 pf p0 p1 Hunf HC Hp Hc' HP2. pfold. apply: ip_ctrans. eauto. pfold_reverse. pfold_reverse.
- move=> c0 c0' c1 c1' pf p0 p1 Hf Hineq Hinv Hineq2 Hinv2. pfold. apply: ip_cplus. eauto. pfold_reverse. pfold_reverse.
- move=> c0 c0' c1 c1' pf p0 p1 Heq HC0 Hinv0 HC1 Hinv1. pfold. apply: ip_cseq. eauto. pfold_reverse. pfold_reverse.
- move=> c0 c1 pf p0 Heq HC Hinv. pfold. apply: ip_cstar. eauto. pfold_reverse.
- move=> _ r2 r' pf p0 Heq [] // Hin. pfold. apply: ip_guard. eauto. eauto.
Qed.


Lemma any_fuel : forall n d, invPred d ->  D_dom d n.
Proof.
elim. move=> d. 
sunfold. elim;eauto;intros.
all: try solve [ apply: D_base; rewrite H //].  
move=> n IH d.
sunfold. elim;eauto;intros.
all: try solve [ apply: D_base; rewrite H //].  
case: H0=>// H0. apply: D_guard. eauto. eauto. eauto.
Qed.


Lemma interp_plus_l : forall n d d0 d1 T (Heq : full_unf d = cplus d0 d1)  (D0 : D_dom d0 n) ( D1 : D_dom d1 n), 
    interpl (D_plus d Heq D0 D1) (up_inl T) = omap up_inl (interpl D0 T).
Proof.
intros. unlock interpl. simpl. erewrite Heq.  done.
Qed.

Definition not_plus (T : upTree ) :=  match T with | up_inl _ | up_inr _ => false | _ => true end.
Definition not_pair (T : upTree ) :=  match T with | up_pair _ _ => false | _ => true end.
Definition not_star (T : upTree ) :=  match T with |  (up_fold (up_inl up_tt)) | (up_fold (up_inr (up_pair _ _))) => false | _ => true end.
Definition not_guard (T : upTree) := match T with | up_pair (up_singl _) _ => false | _ => true end.


Lemma interp_plus_r : forall n d d0 d1 T (Heq : full_unf d = cplus d0 d1)  (D0 : D_dom d0 n) ( D1 : D_dom d1 n), 
    interpl (D_plus d Heq D0 D1) (up_inr T) = omap up_inr (interpl D1 T).
Proof.
intros. unlock interpl. simpl. erewrite Heq.  done.
Qed.

Lemma interp_plus_up_bot : forall n d d0 d1 T (Heq : full_unf d = cplus d0 d1)  (D0 : D_dom d0 n) ( D1 : D_dom d1 n), 
    not_plus T ->
    interpl (D_plus d Heq D0 D1) T = Some up_bot. 
Proof.
intros. unlock interpl. simpl. erewrite Heq. destruct T;ssa. 
Qed.

Lemma interp_seq_none : forall n d d0 d1 T0 T1(Heq : full_unf d = cseq d0 d1)  (D0 : D_dom d0 n) ( D1 : D_dom d1 n), 
    interpl D0 T0 = None -> 
    interpl (D_seq d Heq D0 D1) (up_pair T0 T1) = None. 
Proof.
intros. unlock interpl. simpl.  erewrite Heq. unlock interpl in H. rewrite H. done.
Qed.

Lemma interp_seq_some : forall n d d0 d1 T0 T1 T0' (Heq : full_unf d = cseq d0 d1)  (D0 : D_dom d0 n) ( D1 : D_dom d1 n), 
    interpl D0 T0 = Some T0' -> 
    interpl (D_seq d Heq D0 D1) (up_pair T0 T1) = omap (fun T1' => up_pair T0' T1') (interpl D1 T1).
Proof.
intros. unlock interpl. simpl.  erewrite Heq. 
unlock interpl in H. rewrite H. done. (*erewrite did not work here but rewrite did, why?*)
Qed.

Definition not_seq T := if T is up_pair T0 T1 then false else true.


Lemma interp_seq_bot : forall n d d0 d1 T  (Heq : full_unf d = cseq d0 d1)  (D0 : D_dom d0 n) ( D1 : D_dom d1 n), 
    not_seq T ->
    interpl (D_seq d Heq D0 D1) T = Some up_bot.
Proof.
intros. unlock interpl. simpl. erewrite Heq. 
destruct T;ssa. 
Qed.


Inductive plus_case : upTree -> Prop := 
| pcl T : plus_case (up_inl T)
| pcr T : plus_case (up_inr T)
| pcn T : not_plus T ->  plus_case T.
Hint Constructors plus_case.
Lemma plus_caseP : forall p, plus_case p.
Proof.
case;ssa.
Qed.

Inductive seq_case : upTree -> Prop := 
| upcl T0 T1: seq_case (up_pair T0 T1)
| upcn T : not_seq T ->  seq_case T.
Hint Constructors seq_case.
Lemma seq_caseP : forall p, seq_case p.
Proof.
case;ssa.
Qed.

Inductive star_case : upTree -> Prop := 
| sc0 : star_case (up_fold (up_inl up_tt))
| sc1 T0 T1 : star_case (up_fold (up_inr (up_pair T0 T1)))
| sc2 T : not_star T ->  star_case T.
Hint Constructors star_case.
Lemma star_caseP : forall p, star_case p.
Proof.
case;ssa. case: u;ssa. case : u;ssa. case: u;ssa.
Qed.

Lemma interp_star_some_tt : forall n d d' (Heq : full_unf d = cstar d') (D: D_dom d' n),
    interpl (D_star d Heq D) (up_fold (up_inl up_tt)) = Some (up_fold (up_inl up_tt)).
Proof.
intros. unlock interpl. simpl.  erewrite Heq. done.
Qed.

Lemma interp_star_some_pair : forall n d d' T0 T0' T1 (Heq : full_unf d = cstar d') (D: D_dom d' n),
    interpl D T0 = Some T0' ->
    interpl (D_star d Heq D) (up_fold (up_inr (up_pair T0 T1))) = 
      omap (fun T1' => up_fold (up_inr (up_pair T0' T1'))) (interpl (D_star d Heq D) T1).
Proof.
intros. unlock interpl. simpl.  erewrite Heq. unlock interpl in H. rewrite H. done.
Qed.

Lemma dec_dsl : forall (x y: dsl), x = y \/ x <> y.
Proof. intros. case: (eqVneq x y);auto. move/eqP. auto.
Qed.


Lemma dec_nat : forall (x y: nat), x = y \/ x <> y.
Proof. intros. case: (eqVneq x y);auto. move/eqP. auto.
Qed.



Lemma dsl_refl : forall (x : dsl) (H: x = x), H = @Logic.eq_refl dsl x.
Proof.
intros. apply: eq_proofs_unicity. apply:dec_dsl.
Qed.

Lemma nat_refl : forall (x : nat) (H: x = x), H = @Logic.eq_refl nat x.
Proof.
intros. apply: eq_proofs_unicity. apply:dec_nat.
Qed.
Lemma interp_star_none_pair : forall n d d' T0 T1 (Heq : full_unf d = cstar d') (D: D_dom d' n),
    interpl D T0 = None ->
    interpl (D_star d Heq D) (up_fold (up_inr (up_pair T0 T1))) = None.
Proof.
intros. unlock interpl. simpl. 
(*move: Heq.*)
 (*erewrite Heq. *) 
move: (@Logic.eq_refl _ (full_unf _)). (*The match is applied on an eq_refl, say H, proof, generalize H *)
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: Heq2. rewrite Heq. move=>H2. 
rewrite (dsl_refl H2). unlock interpl in H. rewrite H //.
Qed.

(*Size induction with upTree*)
Lemma interp_star_up_bot : forall n d d' T  (Heq : full_unf d = cstar d') (D: D_dom d' n), not_star T ->
    interpl (D_star d Heq D) T = Some up_bot.
Proof.
intros. unlock interpl. simpl.  erewrite Heq. move: H. 
move Heqn: (upTree_0size T) => n'. move: Heqn. 
wlog: T n' / upTree_0size T <= n'.
move=>HH Hsize Hnot.  apply:HH. 2: eauto. lia. done. clear Heq.
move=>+_.
elim: n' T.
case=>//=.
move=> n0 IH. case=>//=. case=>//=. case=>//=. case=>//=. 
Qed.

Inductive guard_case : upTree -> Prop := 
| gc0 a T : guard_case (up_pair (up_singl a) T)
| gc1 T : not_guard T -> guard_case T.
Hint Constructors guard_case.

Lemma guard_caseP : forall p, guard_case p.
Proof.
case;ssa. case: u;ssa. 
Qed.


Lemma interp_guard_some : forall n n' a d d' T T'  (Heq : full_unf d = guard d') (Heqn: n = n'.+1) (D: D_dom d' n'), 
    interpl D T = Some T' ->
    interpl (D_guard d Heq Heqn D) (up_pair (up_singl a) T) = Some (up_pair (up_singl a) T').
Proof.
intros. unlock interpl. simpl. 
move: (@Logic.eq_refl _ (full_unf _)). (*The match is applied on an eq_refl, say H, proof, generalize H *)
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: (@Logic.eq_refl nat _). 
rewrite {2 3} Heqn. move=>Heqn2.
move: (eq_proofs_unicity dec_nat Heqn Heqn2). 
move=>->.
move: Heqn2. rewrite Heqn. move=>Heqn2.
rewrite (nat_refl Heqn2).  clear Heqn. clear Heqn2.
move: {1  3 4 }Heq2. rewrite Heq /=. (*Avoid touching equality proof in D_guard*)
move=>Heq0.
rewrite (dsl_refl Heq0).  clear Heq0. clear Heq.
unlock interpl in H. rewrite H //.
Qed.

Lemma interp_guard_none : forall n n' a d d' T  (Heq : full_unf d = guard d') (Heqn: n = n'.+1) (D: D_dom d' n'), 
    interpl D T = None ->
    interpl (D_guard d Heq Heqn D) (up_pair (up_singl a) T) = None.  
Proof.
intros. unlock interpl. simpl. 
move: (@Logic.eq_refl _ (full_unf _)). (*The match is applied on an eq_refl, say H, proof, generalize H *)
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: (@Logic.eq_refl nat _). 
rewrite {2 3} Heqn. move=>Heqn2.
move: (eq_proofs_unicity dec_nat Heqn Heqn2). 
move=>->.
move: Heqn2. rewrite Heqn. move=>Heqn2.
rewrite (nat_refl Heqn2).  clear Heqn. clear Heqn2.
move: {1  3 4 }Heq2. rewrite Heq /=. (*Avoid touching equality proof in D_guard*)
move=>Heq0. 
rewrite (dsl_refl Heq0).  clear Heq0. clear Heq.
unlock interpl in H. rewrite H //.
Qed.

Lemma interp_guard_up_bot : forall n n' d d' T  (Heq : full_unf d = guard d') (Heqn: n = n'.+1) (D: D_dom d' n'), not_guard T ->
    interpl (D_guard d Heq Heqn D) T = Some up_bot. 
Proof.
intros. unlock interpl. simpl. 
move: (@Logic.eq_refl _ (full_unf _)). (*The match is applied on an eq_refl, say H, proof, generalize H *)
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: (@Logic.eq_refl nat _). 
rewrite {2 3} Heqn. move=>Heqn2.
move: (eq_proofs_unicity dec_nat Heqn Heqn2). 
move=>->.
move: Heqn2. rewrite Heqn. move=>Heqn2.
rewrite (nat_refl Heqn2).  clear Heqn. clear Heqn2.
move: {1  3 4 }Heq2. rewrite Heq /=. (*Avoid touching equality proof in D_guard*)
move=>Heq0. 
rewrite (dsl_refl Heq0).  clear Heq0. clear Heq.
case:T H;ssa. case:u H;ssa.
Qed.

Lemma interp_stop_pair : forall n d d0 a T1 (Heq: full_unf d = guard d0) (Heqn: n = 0) (D: D_dom d n), interpl (D_stop d Heq Heqn) (up_pair (up_singl a) T1) = None.
Proof.
intros. unlock interpl. simpl. 
move: (@Logic.eq_refl dsl _).
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: (@Logic.eq_refl nat _). 
rewrite {2 3} Heqn //. 
Qed.

Lemma interp_stop_up_bot : forall n d d0 T (Heq: full_unf d = guard d0) (Heqn: n = 0) (D: D_dom d n), not_guard T ->
 interpl (D_stop d Heq Heqn) T = Some up_bot.
Proof.
intros. unlock interpl. simpl. 
move: (@Logic.eq_refl dsl _).
rewrite {2 3} Heq. move=>Heq2.  (*Rewrite RHS of H and scrutinee of the match *)
move: (eq_proofs_unicity dec_dsl Heq Heq2). (*make proof not depend on Heq*)
move=>->. 
move: (@Logic.eq_refl nat _). 
rewrite {2 3} Heqn //. move=>_. case: T H;ssa. case: u H;ssa.
Qed.
 
(*No explosion in interp definition because we use the lock*)
Lemma interp_size : forall n d T T' (D: D_dom d n), interpl D T = Some T' -> event_size T' <= event_size T.
Proof.
refine (fix loop n d T T' D {struct D} := _).
destruct D.
- rewrite interp_base_eq. case;intros;subst.
  apply/interp_base_size. eauto.
- case Heq: (interpl D1 T) => [ T'' | ]. 
  erewrite interp_trans_eq_some. 2: eauto. move=>Heq2.
  move: (loop n d0 T T'' D1 Heq)=>Hint1. 
  move: (loop n d1 _ _ D2 Heq2). lia.
  rewrite interp_trans_eq_none //.
- case: (plus_caseP T). 
 * move=> T0. rewrite interp_plus_l.
   case Heq: (interpl _ _)=>//= [ T'']. case;intros;subst.
   move: (loop _ _ _ _ D1 Heq)=>//.
 * move=> T0. rewrite interp_plus_r.
   case Heq: (interpl _ _)=>//= [ T'']. case;intros;subst.
   move: (loop _ _ _ _ D2 Heq)=>//.
 * move=> T0 Hnot. rewrite interp_plus_up_bot //. case. move=><- /=. lia. 
- case: (seq_caseP T). 
 * move=> T0 T1. 
   case Heq: (interpl D1 T0) =>// [T0' | ].
   erewrite interp_seq_some. 2 : eauto. simpl.
   case Heq2: (interpl D2 T1) =>//= [ T1']. case;intros;subst.
   simpl.
   move: (loop _ _ _ _ _ Heq) (loop _ _ _ _ _ Heq2). lia.
   rewrite interp_seq_none //.
   move=> T0 Hnot. rewrite interp_seq_bot //. case;intros;subst. ssa.
- move Heqn: (upTree_0size T) => n'. move: Heqn. 
  wlog: T n' / upTree_0size T <= n'.
  move=>HH Hsize Hint.  apply:HH. 2: eauto. lia. done. move=>+_.
  elim: n' T T'.
 * move=> T. case: (star_caseP T)=>//. move=> T0 Hnot T' Hsize.
   rewrite interp_star_up_bot //. case;intros;subst. simpl. lia.
 * move=> n0 IH T T'. case: (star_caseP T)=>//.
  ** move=> Hsize. rewrite interp_star_some_tt. case;intros;subst. done.
  ** move=> T0 T1. 
     case Heq: (interpl D T0) =>// [T0' | ].
     erewrite interp_star_some_pair. 2: eauto. 
     case Heq2: ((interpl (D_star d e D) T1))=>// [ T1'].
     move=> Hsize. simpl. case;intros;subst. simpl.
     move: (loop _ _ _ _ _ Heq). intros.
     suff: event_size T1' <= event_size T1. lia.
     apply: IH. simpl in Hsize. lia. done.
     move=> Hsize. rewrite interp_star_none_pair //.
  ** move=> T0 Hnot Hsize. rewrite interp_star_up_bot //. case;intros;subst. simpl. lia.
- case: (guard_caseP T). 
 * move=>a T0.
   case Heq: (interpl D T0) =>// [T0' | ].
   erewrite interp_guard_some. 2: eauto. simpl. case;intros;subst. simpl. 
   move: (loop _ _ _ _ _ Heq). lia.
 * rewrite interp_guard_none //.
 * move=> T0 Hnot. rewrite interp_guard_up_bot //. case;intros;subst. simpl. lia.
- case: (guard_caseP T). 
 * move=>a T0. rewrite interp_stop_pair //. subst.
   apply:D_stop. eauto. done.
 * move=> T0 Hnot. rewrite interp_stop_up_bot //. case;intros;subst. simpl. lia.
   apply:D_stop. eauto. done.
Qed.





(*Require Import Program.Equality.*)
Lemma interp_fuel : forall n (d : dsl) (D: D_dom d n)  (T : upTree), event_size T <= n -> interpl D T.
Proof.
refine (fix loop n d D {struct D} := _).
destruct D. 
- move => T _. rewrite interp_base_eq //.
- move=> T Hsize. 
  move: (loop n d0 D1 T Hsize)=>Hi.
  case Heq : (interpl D1 T) Hi=>// [ T0] _.
  erewrite interp_trans_eq_some. 2: eauto.
  move:  ((interp_size _ _ Heq)). move=> Hsize2.
  have: event_size T0 <= n by lia. move=> Hsize3.
  exact: (loop n d1 D2 T0 Hsize3).
- move=> T. case: (plus_caseP T).
 * move=> T0 Hsize. rewrite interp_plus_l /=.
   simpl in Hsize. move: (loop _ _ D1 _ Hsize). case: (interpl _ _)=>//.
 * move=> T0 Hsize. rewrite interp_plus_r /=.
   simpl in Hsize. move: (loop _ _ D2 _ Hsize). case: (interpl _ _)=>//. 
 * move=> T0 Hnot Hsize. rewrite interp_plus_up_bot //=.
- move=> T. case: (seq_caseP T).
 * move=> T0 T1 Hsize. simpl in Hsize.
   have: event_size T0 <= n. lia. move=>Ht0.
   have: event_size T1 <= n. lia. move=>Ht1.
   move: (loop _ _ D1 _ Ht0) (loop _ _ D2 _ Ht1).
   case Heq: (interpl D1 T0) =>// [ T2 ] _.
   case Heq2: (interpl D2 T1) =>// [ T3 ] _.
   erewrite interp_seq_some;eauto. rewrite Heq2 //.
 * move=> T0 Hnot Hsize. rewrite interp_seq_bot //=. 
- move=> T. move Heqn: (upTree_0size T) => n'. move: Heqn. 
  wlog: T n' / upTree_0size T <= n'.
  move=>HH Hsize Hint.  apply:HH. 2: eauto. lia. done. move=>+_. 
  elim: n' T.
 * move=> T. case: (star_caseP T)=>//. move=> T0 Hnot Hsize.
   rewrite interp_star_up_bot //. 
 * move=> n0 IH T. case: (star_caseP T)=>//.
  ** move=> Hsize. rewrite interp_star_some_tt //. 
  ** move=> T0 T1. 
     case Heq: (interpl D T0) =>// [T0' | ].
     erewrite interp_star_some_pair. 2: eauto. 
     case Heq2: ((interpl (D_star d e D) T1))=>// [ ]. 
     simpl. intros.
     have: upTree_0size T1 <= n0.  lia. intro.
     have: event_size T1 <= n. lia. intro.
     move: (IH T1 H1 H2). rewrite Heq2 //. 
     simpl. intros.
     have: event_size T0 <= n. lia. intros.
     move: (loop n d0 D T0 H1). rewrite Heq //. 
  ** move=> T0 Hnot Hsize. rewrite interp_star_up_bot //. 
- move=> T. case: (guard_caseP T). 
 * move=>a T0.
   case Heq: (interpl D T0) =>// [T0' | ].
   erewrite interp_guard_some. 2: eauto. done. 
 * move=>/= Hsize.  have: event_size T0 <= n' by lia. intro.
   move: (loop n' d0 D T0 H). rewrite Heq //. 
 * move=> T0 Hnot. rewrite interp_guard_up_bot //.
- move=> T. case: (guard_caseP T). 
 * move=>a T0 /= Hsize. subst. lia. 
 * move=> T0 Hnot Hsize. rewrite interp_stop_up_bot //=. 
   subst. apply: D_stop. eauto. done.
Qed.
Check typing.
Check interpl.
Search invPred.
Definition interp_wrap p  (H: invPred  p ) (T : upTree): option upTree := interpl (any_fuel (event_size T) H) T.


Lemma INEQ_unf : forall c0 c1 d, INEQ c0 c1 d -> INEQ c0 c1 (full_unf d).
Proof.
move=>c0 c1 d. sunfold. elim;eauto;intros.
all: try solve [rewrite H; pfold; con=>//].
rewrite H. pfold. econ. done. 
pfold_reverse=>//. 
pfold_reverse=>//. 

rewrite H. pfold. apply:rule_cplus. done.
pfold_reverse=>//. 
pfold_reverse=>//. 


rewrite H. pfold. apply:rule_cseq. done.
pfold_reverse=>//. 
pfold_reverse=>//. 


rewrite H. pfold. apply:rule_cstar. done.
pfold_reverse=>//. 

rewrite H. inv H0.
pfold. 
apply:rule_guard. done. left. done.
Qed.



(*invPred is derived from INEQ, but delay this to have conclusion not depend on proof, disallowing unfolding INEQ*)
Lemma interp_typing : forall d n  (D: D_dom d n) T T' c0 c1, interpl D T = Some T' ->  event_size T <= n -> INEQ c0 c1 d -> typing T c0 ->  typing T' c1.
Proof.
refine (fix loop d n D {struct D} := _).
destruct D.
- move=> T T' c0 c1. rewrite interp_base_eq. case=>Hf. subst.
  move=>_ Hineq. move: Hineq e. sunfold. case.
  all: try solve[intros; rewrite e in e0; inv e0;  eauto].
- move=> T T' c0 c1.
  case Heq: (interpl D1 T) => [T'' |].
  erewrite interp_trans_eq_some. 2: eauto.
  move=> Hint Hsize.
  move/INEQ_unf. rewrite e.
  sunfold=>HH. inv HH. move=> Ht.
  have: event_size T'' <= event_size T.
  move: (interp_size _ _  Heq). lia. move=>Hle0.
  have: event_size T' <= event_size T''.
  move: (interp_size _ _  Hint). lia. move=>Hle1.
  have: event_size T'' <= n. lia. move=>Hle2. inv H.
  punfold_reverse H1. 
  move: (loop _ _ _ _ _ _ _ Hint Hle2 H1)=>Htype. apply: Htype.
  punfold_reverse H0. 
  rewrite interp_trans_eq_none //.
- move=> T T' c0 c1. 
  case: (plus_caseP T).
 * move=> T0. rewrite interp_plus_l.
   case Heq: (interpl D1 T0)=>//= [T1]. case. move=>HT';subst.
   move=>Hsize /INEQ_unf Hineq Ht. rewrite e in Hineq. punfold Hineq. inv Hineq.
   inv Ht. con. inv H. punfold_reverse H0. 
 * move=> T0. rewrite interp_plus_r.
   case Heq: (interpl D2 T0)=>//= [T1]. case. move=>HT';subst.
   move=>Hsize /INEQ_unf Hineq Ht. rewrite e in Hineq. punfold Hineq. inv Hineq.
   inv Ht. con. inv H. punfold_reverse H1. 
 * move=> T0 Hnot _ _ /INEQ_unf. rewrite e. move=>Hineq.  
   punfold Hineq. inv Hineq. move=>Htype. inv Htype.
- move=> T T' c0 c1. 
  case: (seq_caseP T).
 * move=> T0 T1. 
   case Heq: (interpl D1 T0)=>//= [T0' |]. 
   erewrite interp_seq_some. 2:eauto. 
   case Heq2: (interpl D2 T1)=>//= [T1' ]. case. move=>Ht';subst.
   move=>Hsize.  move/INEQ_unf. rewrite e. move=>Hineq. punfold Hineq. inv Hineq.
   inv H.
   move=>Htype. inv Htype. con.
   have: event_size T0 <= n by lia. move=>Hle0.
   punfold_reverse H0.
   have: event_size T1 <= n by lia. move=>Hle1. 
   punfold_reverse H1.
   rewrite interp_seq_none //.
 * move=> T0 Hnot _ _ /INEQ_unf Hineq. rewrite e in Hineq.  punfold Hineq. inv Hineq.
   inv H. move=>Htype. inv Htype.
- move=> T. move Heqn: (upTree_0size T) => n'. move: Heqn. 
  wlog: T n' / upTree_0size T <= n'.
  move=>HH Hsize Hint.  apply:HH. 2: eauto. lia. move=>+_. 
  elim: n' T.
 * move=> T. case: (star_caseP T)=>//. move=> T0 Hnot Hsize.
   move=> T' c0 c1 _ _ /INEQ_unf. rewrite e=>Hineq. punfold Hineq. inv Hineq. inv H.
   move=>Htype. inv Htype.
 * move=> n0 IH T. case: (star_caseP T)=>//.
  ** move=> Hsize T' c0 c1. rewrite interp_star_some_tt //. 
     case. move=>Ht';subst. move=>Hsize2. move/INEQ_unf. rewrite e=>Hineq. punfold Hineq. inv Hineq.
     inv H. move=>Htype. inv Htype. inv H3. eauto. 
  ** move=> T0 T1. 
     case Heq: (interpl D T0) =>// [T0' | ].
     erewrite interp_star_some_pair. 2: eauto. 
     case Heq2: ((interpl (D_star d e D) T1))=>// [ T1']. 
     simpl.
     move=>Hupsize. 

     move=>T' c0 c1 [] Ht';subst. move=>Hsize.
     have: event_size T0 <= n by lia. move=>Hle0.
     have: event_size T1 <= n by lia. move=>Hle1.
     move/INEQ_unf. rewrite e=>Hineq. punfold Hineq. inv Hineq. inv H.
     move=>Htype. inv Htype. inv H3. inv H4. punfold_reverse H0. punfold_reverse Hineq. 
     con. con. con. eauto.  
     apply: IH. 2:eauto. lia. lia. 2:eauto.
     pfold. apply:rule_cstar. eauto. pfold_reverse.
  ** move=> _ T' c0 c1. rewrite interp_star_none_pair //.
  ** move=> T0 Hnot Hsize T' c0 c1 _ _ /INEQ_unf Hineq. rewrite e in Hineq. punfold Hineq. inv Hineq.
     inv H. move=> Htype. inv Htype. inv H3. inv H4. inv H4. 
- move=> T. case: (guard_caseP T). 
 * move=>a T0.
   case Heq: (interpl D T0) =>// [T0' | ].
   erewrite interp_guard_some. 2: eauto. 
   move=> T' c0 c1 [] Ht';subst. move=>Hsize /INEQ_unf. rewrite e. move=>Hineq. punfold Hineq. inv Hineq.
   inv H. inv H0. move=>Htype. inv Htype. con. done. eauto.
 * move=> T' c0 c1. rewrite interp_guard_none //.
 * move=> T0 Hnot T' c0 c1 _ _ /INEQ_unf. rewrite e. move=>Hineq.
   punfold Hineq. inv Hineq. inv H. inv H0. move=>Htype. inv Htype. inv H5.
- move=> T. subst. case: (guard_caseP T). 
 * move=>a T0 T' c0 c1 /=. rewrite interp_stop_pair //. eauto. 
 * move=> T0 Hnot T' c0 c1 _ _ /INEQ_unf. rewrite e. sunfold=>Hineq. inv Hineq. inv H0.
   move=>Htype. inv Htype. inv H5.
Qed.




Lemma interp_flatten : forall d n  (D: D_dom d n) T T' c0 c1, interpl D T = Some T' ->  event_size T <= n -> INEQ c0 c1 d -> typing T c0 ->  uflatten T = uflatten T'. 
Proof.
refine (fix loop d n D {struct D} := _).
destruct D.
- move=> T T' c0 c1. rewrite interp_base_eq. case=>Hf. subst.
  move=>_ Hineq. move: Hineq e. sunfold. case.
  all: try solve[intros; rewrite e in e0; inv e0;  flat_tac;eauto]. 
  intros; rewrite e in e0; inv e0. rewrite abortRinv_i_flat //.
  intros; rewrite e in e0; inv e0. erewrite abortL_i_flat;eauto. 
  intros; rewrite e in e0; inv e0. erewrite abortLinv_i_flat;eauto. 
- move=> T T' c0 c1.
  case Heq: (interpl D1 T) => [T'' |].
  erewrite interp_trans_eq_some. 2: eauto.
  move=> Hint Hsize.
  move/INEQ_unf. rewrite e.
  sunfold=>HH. inv HH. move=> Ht.
  have: event_size T'' <= event_size T.
  move: (interp_size _ _  Heq). lia. move=>Hle0.
  have: event_size T' <= event_size T''.
  move: (interp_size _ _  Hint). lia. move=>Hle1.
  have: event_size T'' <= n. lia. move=>Hle2. inv H.
  punfold_reverse H1. punfold_reverse H0. 
  move: (loop _ _ _ _ _ _ _ Hint Hle2 H1)=>Htype. 
  rewrite -Htype. eauto. 
  apply: (interp_typing D1 Heq Hsize H0). eauto.
  rewrite interp_trans_eq_none //.
- move=> T T' c0 c1. 
  case: (plus_caseP T).
 * move=> T0. rewrite interp_plus_l.
   case Heq: (interpl D1 T0)=>//= [T1]. case. move=>HT';subst.
   move=>Hsize /INEQ_unf Hineq Ht. rewrite e in Hineq. punfold Hineq. inv Hineq.
   simpl. 
   inv Ht. inv H. punfold_reverse H0. 
 * move=> T0. rewrite interp_plus_r.
   case Heq: (interpl D2 T0)=>//= [T1]. case. move=>HT';subst.
   move=>Hsize /INEQ_unf Hineq Ht. rewrite e in Hineq. punfold Hineq. inv Hineq.
   inv Ht. inv H. simpl. punfold_reverse H1. 
 * move=> T0 Hnot _ _ /INEQ_unf. rewrite e. move=>Hineq.  
   punfold Hineq. inv Hineq. move=>Htype. inv Htype.
- move=> T T' c0 c1. 
  case: (seq_caseP T).
 * move=> T0 T1. 
   case Heq: (interpl D1 T0)=>//= [T0' |]. 
   erewrite interp_seq_some. 2:eauto. 
   case Heq2: (interpl D2 T1)=>//= [T1' ]. case. move=>Ht';subst.
   move=>Hsize.  move/INEQ_unf. rewrite e. move=>Hineq. punfold Hineq. inv Hineq.
   inv H.
   move=>Htype. inv Htype. simpl. 
   f_equal.
   have: event_size T0 <= n by lia. move=>Hle0.
   punfold_reverse H0.
   have: event_size T1 <= n by lia. move=>Hle1. 
   punfold_reverse H1.
   rewrite interp_seq_none //.
 * move=> T0 Hnot _ _ /INEQ_unf Hineq. rewrite e in Hineq.  punfold Hineq. inv Hineq.
   inv H. move=>Htype. inv Htype.
- move=> T. move Heqn: (upTree_0size T) => n'. move: Heqn. 
  wlog: T n' / upTree_0size T <= n'.
  move=>HH Hsize Hint.  apply:HH. 2: eauto. lia. move=>+_. 
  elim: n' T.
 * move=> T. case: (star_caseP T)=>//. move=> T0 Hnot Hsize.
   move=> T' c0 c1 _ _ /INEQ_unf. rewrite e=>Hineq. punfold Hineq. inv Hineq. inv H.
   move=>Htype. inv Htype.
 * move=> n0 IH T. case: (star_caseP T)=>//.
  ** move=> Hsize T' c0 c1. rewrite interp_star_some_tt //. 
     case. move=>Ht';subst. move=>Hsize2. move/INEQ_unf. rewrite e=>Hineq. punfold Hineq. 
  ** move=> T0 T1. 
     case Heq: (interpl D T0) =>// [T0' | ].
     erewrite interp_star_some_pair. 2: eauto. 
     case Heq2: ((interpl (D_star d e D) T1))=>// [ T1']. 
     simpl.
     move=>Hupsize. 
     move=>T' c0 c1 [] Ht';subst. move=>Hsize /INEQ_unf. rewrite e.
     move=>Hineq. punfold Hineq. inv Hineq. inv H. move=>Htype. inv Htype.
     inv H3. inv H4. simpl. f_equal.
     have: event_size T0 <= n by lia. move=>Hle0. punfold_reverse H0.
     have: event_size T1 <= n by lia. move=>Hle1. punfold_reverse H0. punfold_reverse Hineq. 
     apply:IH. lia. eauto. lia. 2 : eauto. pfold. apply:rule_cstar. eauto.  pfold_reverse.
  ** move=> _ T' c0 c1. rewrite interp_star_none_pair //.
  ** move=> T0 Hnot Hsize T' c0 c1 _ _ /INEQ_unf Hineq. rewrite e in Hineq. punfold Hineq. inv Hineq.
     inv H. move=> Htype. inv Htype. inv H3. inv H4. inv H4. 
- move=> T. case: (guard_caseP T). 
 * move=>a T0.
   case Heq: (interpl D T0) =>// [T0' | ].
   erewrite interp_guard_some. 2: eauto. 
   move=> T' c0 c1 [] Ht';subst. move=>Hsize /INEQ_unf. rewrite e. move=>Hineq. punfold Hineq. inv Hineq.
   inv H. inv H0. move=>Htype. inv Htype. simpl. f_equal. eauto. 
 * move=> T' c0 c1. rewrite interp_guard_none //.
 * move=> T0 Hnot T' c0 c1 _ _ /INEQ_unf. rewrite e. move=>Hineq.
   punfold Hineq. inv Hineq. inv H. inv H0. move=>Htype. inv Htype. inv H5.
- move=> T. subst. case: (guard_caseP T). 
 * move=>a T0 T' c0 c1 /=. rewrite interp_stop_pair //. eauto. 
 * move=> T0 Hnot T' c0 c1 _ _ /INEQ_unf. rewrite e. sunfold=>Hineq. inv Hineq. inv H0.
   move=>Htype. inv Htype. inv H5.
Qed.


(*Maybe be state this with informative proofs as well*)
Lemma interp_spec : forall c0 c1 d T, INEQ c0 c1 d -> typing T c0 ->  exists (n : nat) (D: D_dom d n) T', interpl D T = Some T' /\ typing T' c1 /\ uflatten T = uflatten T'.  
Proof.
move=> c0 c1 d T Hineq Ht. exists (event_size T).
move :  ((any_fuel (event_size T) (to_invPred Hineq)))=>D.
have: event_size T <= event_size T by lia. move=>Hle.
move: (interp_fuel D T Hle).
case Heq:(interpl _ _) =>// [ T'] _.
move: (interp_typing D  Heq Hle Hineq Ht)=>Htype.
exists D,T'. con.
apply: Heq. con. done.
move: (interp_flatten _ Heq Hle  Hineq Ht)=>//.
Qed.


Lemma INEQ_sound : forall c0 c1 d, INEQ c0 c1 d -> (forall s, Match s c0 -> Match s c1).
Proof.
move=> c0 c1 d Hineq s Hmatch. 
case: (exists_pTree Hmatch)=> x /andP [] /typingP1 Htype /eqP Hflat. subst. 
move: (interp_spec Hineq Htype). move=>[] n [] D [] T' [] Hint [] Htype2 Hflat. 
rewrite Hflat.
apply: pTree_Match. done.
Qed.















(*Definition mod_ACI (p : regex -> bool) (r : regex)  := exists x, ACI r x /\ p x.*)

Definition sub {B : eqType} (p0 p1: B -> bool) := (forall x, p0 x  -> p1 x)  /\ (exists x, p1 x /\ ~~ p0 x). 

(*Lemma sub_aci_mon : forall (p0 p1 : regex -> bool), *)  

Definition finite_pred {B: eqType} (p : B-> bool) n := exists (l : seq B), size l <= n /\ forall x, p x -> x \in l.

Lemma preserve_fin : forall (B : eqType) (p p' : B -> bool) n, finite_pred p n -> sub p' p -> exists n', n' < n /\ finite_pred p' n'.
Proof. 
intros. inv H.
rewrite /finite_pred.  ssa. subst. 
elim: x n p0 p' H H0 H1 H2.
- ssa. inv H0. ssa. apply H2 in H4. ssa.
- intros. ssa.  inv H1. ssa.
  destruct (eqVneq a x).  subst.
  exists (size l). ssa. exists l. ssa. intros.
  apply H4 in H7 as H7'. apply H3 in H7' as H7''.  rewrite !inE in H7''. lo.
  rewrite H7 in H6. ssa.
  destruct (p0 a) eqn:Heqn.
 * move Heq : (fun x => ( x!= a) && p0 x) => /= p0'. 
   move Heq2 : (fun x => ( x!= a) && p' x) => /= p''. 
   have: finite_pred p0' n.-1. inv H0. ssa.  exists (rem a x0). ssa. rewrite size_rem //. destruct (size x0) eqn:Heqn2=>//.  lia.
   eauto. ssa. rewrite mem_rem //.  eauto. move=>Hfin.
   have: sub p'' p0'. inv H1. ssa. con. intros. ssa. 
   exists x. ssa. rewrite neg_sym //. move=>Hsub.
   have: size l <= n.-1. lia. move=>Hsize.
   have: forall x, p0' x -> x \in l. subst. ssa. apply H3 in H9 as H9'.  rewrite !inE in H9'. lo.
   move=>Hin.
   move:(H _ _ _ Hfin Hsub Hsize Hin). subst. ssa.
   exists x0.+1. ssa. lia. exists (a::x1).   ssa. ssa.
   destruct (eqVneq x2 a). subst. done. rewrite inE. apply/orP. right. apply/H9. ssa.
 * have: forall x, p0 x -> x \in l. intros. apply H3 in H7 as H7'. rewrite !inE in H7'. lo. rewrite Heqn in H7. done.
   move=> Hin. have: size l <= n. lia. move=>Hsize.
   move: (H _ _ _ H0 H1 Hsize Hin). ssa. exists x0. ssa. exists x1. ssa.
Qed.

Lemma fin_0 : forall (B : eqType) (p : B -> bool), finite_pred p 0 -> ~ exists p', sub p' p.
Proof.
intros. intro. ssa. 
move: (preserve_fin H H0). ssa.
Qed.

Inductive D_bisim :  (pder -> bool) -> pder -> Prop := 
| Db_next p l : (forall a, D_bisim (fun x => (x != l) && p x) (pd_l a l)) -> p l -> D_bisim p l
| Db_stop p l : ~~ (p l) -> D_bisim p l.

Lemma D_bisim_exists : forall l, exists p, D_bisim p l.
Proof.
intros.
move Heq: (fun x => all (fun y => y \in pi_l x) x) => p. exists p.
have : Acc sub p. 
have: (size ( finite_pred p n. 
econ. rewrite /finite_pred. simpl.
subst.
Check Acc_rect.

apply Acc_rect. 
(forall y, y \in x -> y \in pi_l x)).

(*

p_enum := pi(r0,r1)
finite_pred p_enum
p0 := (r0,r1)
p_enum \ p0  < p_enum


*)



(*Inductive ACI : regex -> regex -> Prop :=
| ACI_refl r : ACI r r
| ACI_assoc r0 r1 r2 : ACI (r0 _;_ r1 _;_ r2) (r0 _;_ (r1 _;_ r2))
| ACI_idemp r: ACI (r _+_ r ) r.
Hint Constructors ACI.

(*Hint Constructors ACI.*)
Inductive IndContains : list (regex * regex) -> regex -> regex -> Prop := 
| IC0 c0 c1 l : (forall e, IndContains ((c0,c1)::l) (e \ c0) (e \ c1)) ->  (nu c0 -> nu c1) -> IndContains l c0 c1
| IC1 x y c0 c1 l : ACI c0 x  -> ACI c1 y -> (x,y) \in l -> IndContains l c0 c1.
Hint Constructors IndContains.*)
Definition base r := r::Eps::Empt::nil.
Fixpoint regex_enum r := (base r)++
match r with 
| Eps => nil
| Empt => nil 
| Event _ => nil 
| Plus r0 r1 => compose (regex_enum r0) (regex_enum r1) Plus
| Seq r0 r1 => (compose (map (fun x => x _;_ r1)(regex_enum r0)) (regex_enum r1) Plus) ++ (regex_enum r1)
| Star r0 => map (fun x => x _;_ Star r0 )(regex_enum r0)
end.





(*Lemma reg_enum : regex_enum Eps = base Eps.
Proof. done.
Qed.*)

Lemma base_eq r : base r = r :: Eps :: Empt :: nil. 
Proof. done.
Qed.

Lemma in_same (B : eqType) (b : B) l x : x \in b::b::l = (x \in b::l).
Proof.
rewrite !inE. lia.
Qed.
Lemma in_same2 (B : eqType) (b b' : B) l x : x \in b::b'::b::l = (x \in b'::b::l).
Proof.
rewrite !inE. lia.
Qed.
Let eqs := (base_eq,in_same,in_same2).


Ltac rlo := repeat lo.
Lemma selfe : forall r, r \in regex_enum r.
Proof.
elim;ssa.
Qed.
Hint Resolve selfe.

Lemma mem_compose2 : forall aa bb l,   l \in compose aa bb Seq -> exists a b, l = Seq a b /\  a \in aa /\ b \in bb.
Proof. elim;intros. done. 
move : H0=>/=. rewrite mem_cat. move/orP. case. move/mapP=>[] //=. intros. inversion q. subst. 
econ. econ.  eauto.

move/H. case. ssa. subst. econ. econ. eauto.
Qed.

Lemma mem_compose_plus : forall aa bb l,   l \in compose aa bb Plus -> exists a b, l = Plus a b /\  a \in aa /\ b \in bb.
Proof. elim;intros. done. 
move : H0=>/=. rewrite mem_cat. move/orP. case. move/mapP=>[] //=. intros. inversion q. subst. 
econ. econ.  eauto.

move/H. case. ssa. subst. econ. econ. eauto.
Qed.



(*Definition INEQ_bot := paco3 c_ineq bot3.*)
Lemma mem_Empt : forall r, Empt \in regex_enum r.
Proof. case;ssa.
Qed.
Hint Resolve mem_Empt. 

(**)

Lemma in_help :   exists x : regex, ACI Eps x /\ x \in [:: Eps; Eps; Empt].
Proof.
intros. econ. con. apply:ACI_r. done.
Qed.
Hint Resolve in_help.

Lemma in_help1 :  forall r, r \in regex_enum Empt -> exists x : regex, ACI r x /\ x \in [:: Eps; Eps; Empt].
Proof.
intros. ssa. rewrite eqs !inE in H. lo.   eauto.
Qed.
Hint Resolve in_help1.
Lemma in_help2 :  forall r, r \in regex_enum Eps -> exists x : regex, ACI r x /\ x \in [:: Eps; Eps; Empt].
Proof.
intros. ssa. rewrite eqs !inE in H. lo.   
Qed.
Hint Resolve in_help2.
Lemma in_help3 :  forall r, r \in regex_enum Eps -> exists x : regex, ACI r x /\ x \in [:: Empt; Eps; Empt].
Proof.
intros. ssa. rewrite eqs !inE in H. lo.    eauto. eauto.
Qed.
Hint Resolve in_help3.

Lemma in_help4 :  forall r e, r \in regex_enum (Event e) -> exists x : regex, ACI r x /\ x \in [:: Event e; Eps; Empt].
Proof.
intros. ssa. rewrite !inE in H. lo.    eauto.  lo. ssa. eauto. eauto.
Qed.
Hint Resolve in_help4.
Lemma in_help5 :  forall r e, r \in regex_enum (Eps) -> exists x : regex, ACI r x /\ x \in [:: Event e; Eps; Empt].
Proof.
intros. ssa. rewrite !inE in H. lo.    eauto.  lo. 
Qed.
Hint Resolve in_help5.
Lemma in_help6 :  forall r e, r \in regex_enum (Empt) -> exists x : regex, ACI r x /\ x \in [:: Event e; Eps; Empt].
Proof.
intros. ssa. rewrite !inE in H. lo.    eauto.  lo. 
Qed.
Hint Resolve in_help6.

Lemma test_test: forall r0 r1 r2, r1 \in regex_enum r0 -> r2 \in regex_enum r1 -> exists x, ACI r2 x /\ x \in regex_enum r0.
Proof.
elim;ssa.
- rewrite !inE in H. lo. eauto. 
  lo. eauto. rewrite !inE in H. lo. eauto. lo.  eauto.
-  rewrite !inE in H. lo. lo.  
- rewrite !inE in H1. lo. ssa. rewrite !inE in H2. lo. econ. con. apply:ACI_r. done.
  lo. econ. con. apply:ACI_r. done.
  lo. econ. con. apply:ACI_r. done.
  apply mem_compose_plus in H5. ssa. subst.
  econ. con. apply:ACI_r. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  apply/mem_compose. done. done.
  lo. ssa. rewrite eqs in H2. rewrite !inE in H2. lo. econ. con. apply:ACI_r. done.
  econ. con. apply:ACI_r. done.
  lo. ssa. rewrite eqs !inE in H2. lo. lfin. lo. lfin.
  apply mem_compose_plus in H5. ssa. subst. ssa.
  lo. inv H5. rewrite !inE in H2. lo. ssa.
  lfin. lo. lfin. lo. lfin.
  apply mem_compose_plus in H10. ssa. subst.
  econ. con. apply:ACI_r. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  apply/mem_compose. done. done.
  apply mem_compose_plus in H5. ssa. inv H5.
  rewrite !inE in H2. lo.
  econ. con. apply:ACI_r. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  apply/mem_compose. done. done.
  lo. lfin. lo. lfin.
  apply mem_compose_plus in H12. ssa. subst. 
  move: (H _ _ H8 H13) (H0 _ _ H9 H14). ssa.
  exists (x4 _+_ x3). con. eauto. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
    apply/mem_compose.  eauto. eauto.

- rewrite !inE in H1. lo. ssa. rewrite !inE in H2. lo. ssa.
  lfin. lo. lfin. lo. lfin. rewrite mem_cat in H5. lo.
  apply mem_compose_plus in H6. ssa. destruct (mapP H7). subst.
  econ. con. apply:ACI_r. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left. apply/mem_compose.  apply/map_f. done. done.
  lfin.
  lo. ssa. rewrite eqs !inE in H2. lo. lfin.  lfin.
  lo. rewrite !inE in H2. lo. lfin. lo. lfin. lfin.
  rewrite mem_cat in H5. lo.
  apply mem_compose_plus in H6. ssa. subst. 
  destruct (mapP H7). subst. ssa.
  destruct (mapP H7).  inv H10.
  rewrite !inE in H2. lo.
  lfin. lo. lfin. lo. lfin.
  rewrite !mem_cat in H13. lo.
  destruct (mapP H14). subst. 
  clear H13 H12 H11.
  move: (H0 _ _ H8 H15). ssa.
  exists (x _;_ r1 _+_ x2). con. eauto. 
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left. apply/mem_compose. apply/map_f. done. done.
  clear H12 H13 H2 H11.
  lo. destruct (mapP H2). subst. 
  move: (H0 _ _ H8 H11). ssa. admit.



  lo. destruct (mapP H11). subst.
  move: (H0 _ _ H8 H12). ssa. 
  exists x2. con. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. right. done.

  apply mem_compose_plus in H11. ssa. subst. 
  move: (H0 _ _ H8 H13). ssa. 
  rewrite mem_cat in H12. lo.
  apply mem_compose_plus in H16.  ssa. subst.
  destruct (mapP H17). subst.
  move: (H _ _ H6 H16). ssa. subst.
  ex
    
  rewrite mem_cat in H11.
subst. destruct (mapP H9). subst.

  exists (Empt _;_ r1 _+_  (Eps _+_ x2)). con. apply:ACI_t. 2:{  apply:ACI_t. 2: {  apply:ACI_p. apply:ACI2. apply:ACI_r. } 
                                                                       apply:ACI_p. apply:ACI_r. apply:ACI_p. apply:ACI_r. apply:H12. } 
  apply:ACI_t. 2: { 
  
                                                                       apply:ACI_r. } eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left. apply:mem_compose. apply/map_f. done.

  apply mem_compose_plus in H8. ssa. subst. destruct (mapP H9). subst.
  lfin.
  apply

e

  move: (H x r0 H6).
  move: (H0 r3 r3). (selfe r3) (selfe r3)). (selfe r2) H2).
lo. ssa. rewrite !inE in H2. lo.
  move: (H _ (selfe r0)).
clear
ssa.
ssa. rewrite eqs in H0. 
  rewrite !inE in H0. lo. eauto. lo. ssa. rewrite eqs !inE in H0.  lo. eauto. ssa
ssa. econ. con. apply:ACI_r. done.
  econ. con. apply:ACI_r. done.
  lo. ssa. rewrite eqs in H0. rewrite !inE in H0. lo. ssa. econ. con. apply:ACI_r. done.
  econ. con. apply:ACI_r. done. ssa. rewrite eqs in H0.
  rewrite !inE in H0.  lo. econ. con. apply:ACI_r. done. 
  lo. econ. con. apply:ACI_r. done. 
  rewrite !inE in H. lo. ssa. rewrite eqs in H0. rewrite !inE in H0. lo. ssa. econ. con. apply:ACI_r. done.
  lo. econ. con. apply:ACI_r. done. lo. ssa. rewrite eqs in H0.
  clear H . 
  rewrite eqs in H0. rewrite eqs in H0.

Lemma in_enum : forall r0 r1 e, r1 \in regex_enum r0 -> exists x, ACI (e \r1) x /\ x \in regex_enum r0.
Proof.
elim;rewrite /= ?eqs;intros. 
- exists (e \ r1).  rewrite !eqs !inE in H. lo. 
- exists (e\ r1).  rewrite eqs !inE in H. rlo. 
- exists (e\r1).  rewrite !inE in H. lo. ssa. rifliad;ssa. lo.
- rewrite !inE in H1. lo. simpl. 
  move: (H r0 e (selfe r0)) (H0 r1 e (selfe r1)). ssa.
  exists (x0 _+_ x). con. eauto.
  rewrite inE in H1. lo. simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  apply/mem_compose.  eauto. eauto. 
  apply mem_compose_plus in H6. ssa. inv H6. right.
  apply/mem_compose. eauto. eauto.
  lo. ssa. econ. con. con. done.
  lo. ssa. econ. con. apply:ACI_r. done.  
  apply mem_compose_plus in H4. ssa. subst. 
  move: (H x e H5) (H0 x0 e H6). ssa.
  exists (x2 _+_ x1). ssa. 
  right. apply/mem_compose. eauto. eauto.
- rewrite !inE in H1. lo. simpl.
  destruct (nu _) eqn:Heqn. 
* move: (H r0 e (selfe r0)) (H0 r1 e (selfe r1)). ssa.
  exists (x0 _;_ r1 _+_ x). con. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left. 
  apply/mem_compose. apply/map_f. eauto. eauto. 
* move: (H r0 e (selfe r0)). ssa.
  exists (x _;_ r1 _+_ Empt).  con. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left.
  apply/mem_compose. apply/map_f. eauto. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  rewrite mem_cat in H4. lo.
  apply mem_compose_plus in H5. ssa. subst. 
  destruct (mapP H6). subst. simpl.
  destruct (nu _) eqn:Heqn;ssa.
  move: (H x1 e H5) (H0 x0 e H7). ssa.
  move: (H0 r1 e (selfe r1)). ssa.
  exists (x2 _;_ r1 _+_ x3 _+_ x). con. (* apply: ACI_t. 2: { eapply ACI_p. apply ACI_r. apply:ACI_I. }*)
  eauto.
  simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. left.
  apply/mem_compose. 2:eauto. admit.

  move: (H x1 e H5) (H0 _ e H7). ssa. 
  exists ((x2 _;_ r1 _+_  x)). con. eauto.
  simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. left.
  apply/mem_compose. apply/map_f. done. eauto.

  move: (H0 _ e H5). ssa.
  exists x. con. done.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. right. eauto.
rewrite mem_cat. apply/orP. left. apply/mem_compose.
  apply/map_f. eauto. eauto. eauto.

- rewrite !inE in H0. lo. ssa.
  move: (H r0 e (selfe r0)). ssa.
  exists (x _;_ Star r0). ssa. apply/map_f. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  destruct (mapP H3). subst. ssa.
  destruct (nu _) eqn:Heqn;ssa.
  move: (H x e H4) (H  _ e (selfe r0)). ssa.
  exists (x1 _;_ (Star r0) _+_ x0 _;_ (Star r0)). con. eauto.
  simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. left. apply/mem_compose. apply/map_f. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. apply/map_f. eauto.
  move: (H x e H4). ssa.
  exists (x0 _;_ Star r0 _+_ Empt). econ. eauto.
  rewrite !inE.
  apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat.
  apply/orP. left. apply/mem_compose. apply/map_f. eauto.
  done.
Qed.




Lemma in_enum : forall r0 r1 e, r1 \in regex_enum r0 -> exists x, ACI (e \r1) x /\ x \in regex_enum r1.
Proof.
elim;rewrite /= ?eqs;intros. 
- exists (e \ r1).  rewrite !eqs !inE in H. lo. 
- exists (e\ r1).  rewrite eqs !inE in H. rlo. 
- exists (e\r1).  rewrite !inE in H. lo. ssa. rifliad;ssa. lo.
- rewrite !inE in H1. lo. simpl. 
  move: (H r0 e (selfe r0)) (H0 r1 e (selfe r1)). ssa.
  exists (x0 _+_ x). con. eauto.
  rewrite inE in H1. lo. simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  apply/mem_compose.  eauto. eauto. 
   apply mem_compose_plus in H6. ssa. inv H6. right.
  apply/mem_compose. eauto. eauto.
  lo. ssa. econ. con. con. done.
  lo. ssa. econ. con. apply:ACI_r. done.  
  apply mem_compose_plus in H4. ssa. subst. 
  move: (H x e H5) (H0 x0 e H6). ssa.
  exists (x2 _+_ x1). ssa. 
  right. apply/mem_compose. eauto. eauto.
- rewrite !inE in H1. lo. simpl.
  destruct (nu _) eqn:Heqn. 
  move: (H r0 e (selfe r0)) (H0 r1 e (selfe r1)). ssa.
  exists (x0 _;_ r1 _+_ x). con. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left. 
  apply/mem_compose. apply/map_f. eauto. eauto. 
  move: (H r0 e (selfe r0)). ssa.
  exists (x _;_ r1 _+_ Empt).  con. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite mem_cat. apply/orP. left.
  apply/mem_compose. apply/map_f. eauto. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  rewrite mem_cat in H4. lo.
  apply mem_compose_plus in H5. ssa. subst. 
  destruct (mapP H6). subst. simpl.
  destruct (nu _) eqn:Heqn;ssa.
  move: (H x1 e H5) (H0 x0 e H7). ssa.
  move: (H0 r1 e (selfe r1)). ssa.
  exists (x2 _;_ r1 _+_ x3 _+_ x). con. eauto.
  simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. right.
  apply/orP. right. apply/orP. right.
  apply/mem_compose. rewrite mem_cat. apply/orP. left. apply/mem_compose.
  apply/map_f. eauto. eauto. eauto.

  move: (H x1 e H5) (H0 _ e H7). ssa. 
  exists ((x2 _;_ r1 _+_  Empt) _+_ x ). con. eauto.
  simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. right.
  apply/orP. right. apply/orP. right. 
  apply/mem_compose. rewrite mem_cat. apply/orP. left. apply/mem_compose.
  apply/map_f. eauto. eauto. eauto.

- rewrite !inE in H0. lo. ssa.
  move: (H r0 e (selfe r0)). ssa.
  exists (x _;_ Star r0). ssa. apply/map_f. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  lo. ssa. econ. con. apply:ACI_r. done.
  destruct (mapP H3). subst. ssa.
  destruct (nu _) eqn:Heqn;ssa.
  move: (H x e H4) (H  _ e (selfe r0)). ssa.
  exists (x1 _;_ (Star r0) _+_ x0 _;_ (Star r0)). con. eauto.
  simpl. rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right.
  rewrite !mem_cat. apply/orP. left. apply/mem_compose. apply/map_f. eauto.
  rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. apply/map_f. eauto.
  move: (H x e H4). ssa.
  exists (x0 _;_ Star r0 _+_ Empt). econ. eauto.
  rewrite !inE.
  apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat.
  apply/orP. left. apply/mem_compose. apply/map_f. eauto.
  done.
Qed.


Lemma seq_der : forall r r' a, ACI (a \ (r _;_ r'))  ((a \ r) _;_ r'  _+_ (o(r) _;_ a \ r')).
Proof. intros. simpl.
rewrite /o. destruct (nu _) eqn:Heqn. simpl. apply:ACI_p. done. done.
apply: ACI_t. 2 :  { apply:ACI_p. done. apply:ACI3. }  apply:ACI4.
Qed.






Lemma coerce_enum : forall r0 r1 d e, r1 <(bot3)= \big[Plus/Empt]_(a <- regex_enum r0) a ~> d -> 
                             exists d', (e \ r1) <(bot3)= \big[Plus/Empt]_(a <- regex_enum r0) a ~> d'.
Proof.
elim;ssa.
move: H. rewrite !big_cons !big_nil /=. intros.
move=> r0 r1 d e H.
elim: H e;eauto;intros.
- econ. simpl. 

Fixpoint rflatten r := 
match r with 
| Plus r0 r1 => (rflatten r0) ++ (rflatten r1)
| Seq r0 r1 => map (fun x0 => x0 _;_ r1 ) (rflatten r0)
| _ => r::nil
end.

Lemma big_cat_ACI : forall l l', ACI (\big[Plus/Empt]_(x <- l++l') x) ((\big[Plus/Empt]_(x <- l) x) _+_ (\big[Plus/Empt]_(x <- l') x)).  
Proof.
elim;ssa. rewrite big_nil. eauto. 
rewrite !big_cons.
apply:ACI_t. apply:ACI_p. apply:ACI_r. apply/H. 
apply:ACI_t. apply: ACI_sym. apply: ACI_AP. apply:ACI_p. apply:ACI_p. eauto. eauto. eauto.
Qed.



Lemma ACI_factor_seq_r : forall (B: eqType) l (P: B -> regex) c, ACI
(\big[Plus/Empt]_(a <- l) (P a _;_ c)) ((\big[Plus/Empt]_(a <- l) (P a)) _;_ c).
Proof.
move=> B +P c. elim=>//=. rewrite !big_nil //. 
move=> a l IH. rewrite !big_cons.
apply:ACI_t. 2:{ apply:ACI_sym. apply: ACI_dist. }  
eauto.
Qed.

Lemma rflatten_ACI : forall r, ACI r (\big[Plus/Empt]_(x <- (rflatten r) ) x).
Proof.
elim;ssa.
- rewrite big_cons big_nil. eauto.
- rewrite big_cons big_nil. eauto.
- rewrite big_cons big_nil. eauto. apply:ACI_t. apply:ACI_p. apply:H. apply:H0.
  apply:ACI_sym. apply:big_cat_ACI.
- apply:ACI_t. apply:ACI_s. apply:H. apply:H0.
  apply:ACI_t. 2: { apply: ACI_sym. rewrite map_big_plus.  apply:ACI_factor_seq_r. } simpl.
  apply:ACI_s. done. apply:ACI_sym. done.
- rewrite !big_cons !big_nil. eauto.
Qed.


Lemma rflatten_combine : forall r r0 r1, r0 \in rflatten r -> r1 \in rflatten r -> r0 _+_ r1 \in rflatten r.
Proof.
elim;ssa. admit. admit. admit.
rewrite !mem_cat in H1 H2. destruct (orP H1). 
destruct (orP H2). admit.

Notation "r <ACI= r'" := ?
Lemma upper_bound : forall r, exists l, forall r', r' <R= r -> r' \in l

Lemma coerce_enum : forall  (s \\ r1) <R= \big[Plus/Empt]_(a <- regex_enum r) a




Lemma coerce_enum : forall r0 r1, r1 <R= \big[Plus/Empt]_(a <- regex_enum r0) a -> 
                             (e \ r1) <R= \big[Plus/Empt]_(a <- regex_enum r0) a


Lemma enum_closed2 : forall r0 r1 r2 e, r1 \in regex_enum r0 -> r2 \in rflatten (derive e r1) -> r2 \in regex_enum r0.
Proof.
elim;ssa. rewrite inE in H. destruct (orP H). norm_eqs. ssa. rewrite inE in H0. norm_eqs. auto.
rewrite !inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite !inE in H0. norm_eqs. eauto.
norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.
 rewrite inE in H. destruct (orP H). norm_eqs. ssa. rewrite inE in H0. norm_eqs. auto.
rewrite !inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite !inE in H0. norm_eqs. eauto.
norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.
 rewrite inE in H. destruct (orP H). norm_eqs. ssa. 
destruct (eqVneq s e). subst. rewrite inE in H0. norm_eqs. eauto. rewrite inE in H0. norm_eqs. eauto.
rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite inE in H0. norm_eqs. 
rewrite eqxx. lia. rewrite inE in H2. norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.

rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite mem_cat in H2. destruct (orP H2).
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
apply: H. 2 : eauto. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
rewrite inE in H3. destruct (orP H3). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia.
rewrite inE in H4. destruct (orP H4). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia.
rewrite mem_cat in H5. destruct (orP H5). 
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
eauto.
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.


- rewrite inE in H1. destruct (orP H1). norm_eqs. ssa.
destruct (nu _) eqn:Heqn. ssa. rewrite mem_cat in H2. destruct (orP H2). 
destruct (mapP H3). subst. right. apply/orP. right. apply/orP. right. 
rewrite mem_cat. apply/orP. left. apply/mapP. econ. 2:eauto. apply:H. apply:selfe. apply:H4.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto. clear H1. ssa.

destruct (mapP H2). subst. destruct (mapP H2). inv H4. left. apply/mapP. econ.
2:eauto. eauto.


rewrite inE in H3. destruct (orP H3); norm_eqs; ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H3.
rewrite inE in H4. destruct (orP H4). norm_eqs. ssa. rewrite !inE in H2. norm_eqs. rewrite eqxx. lia.
rewrite mem_cat in H3. destruct (orP H3). destruct (mapP H5). subst. ssa.

destruct (nu _) eqn:Heqn. ssa.
rewrite mem_cat in H2. destruct (orP H2). destruct (mapP H7). subst.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
apply/map_f. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto. ssa.
destruct (mapP H2). subst. ssa. destruct (mapP H2).  inv H9.
right. rewrite mem_cat. apply/orP. left. apply/map_f. eauto.
right. 
apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right.  eauto. 

- rewrite !inE in H0. destruct (orP H0). norm_eqs. ssa. destruct (mapP H1). subst. right.
apply/orP. right. apply/orP. right. apply/map_f. eauto.
destruct (orP H2). norm_eqs. ssa. 
rewrite !inE in H1. norm_eqs. rewrite eqxx. lia.
destruct (orP H3). norm_eqs. ssa. rewrite inE in H1. norm_eqs.
right. rewrite eqxx. lia. 
destruct (mapP H4). norm_eqs. 
ssa. destruct (nu _) eqn:Heqn. rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H6).
subst. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H6). subst. 
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H1). subst.
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
Qed.


(*Definition antimorov_l c := proj_sig (derive_unfold_coerce_l_aux bot3 c).
Definition antimorov_r c := proj_sig (derive_unfold_coerce_r_aux bot3 c).*)


(*Lemma ACI_l_c_proof : forall r0 r1, ACI r0 r1 -> { d| INEQ r0 r1 d}.
Proof. Admitted.
Definition ACI_l r0 r1 (H: ACI r0 r1) := proj_sig (ACI_l_c_proof  H).

Lemma ACI_r_c_proof : forall r0 r1, ACI r0 r1 -> { d| INEQ r1 r0 d}.
Proof. Admitted.
Definition ACI_r r0 r1 (H: ACI r0 r1) := proj_sig (ACI_r_c_proof H).

Lemma nu_proof : forall r0 r1, (nu r0 -> nu r1) -> { d | INEQ (o r0) (o r1) d}.
Proof. Admitted.

Definition nu_c r0 r1 (H: nu r0 -> nu r1) := proj_sig (nu_proof r0 r1 H).*)

Definition sum_coerce (f : A -> dsl) := \big[cplus/cid]_(a : A) (guard (f a)).
 (*(forall x y, (x,y) \in l -> INEQ x y (F (x,y))) -> *) 

Inductive BuildCoerce : seq (regex * regex ) -> regex -> regex -> dsl -> Prop := 
| BC0 l r0 r1 r0' r1' d d' d0 d1 : c_ineq bot3 r0 r0' d0 -> c_ineq bot3 r1' r1 d1 ->  BuildCoerce l r0' r1' d' ->
                                                                 d = ctrans (ctrans d0 d') d1 ->
                                                                 BuildCoerce l r0 r1 d
| BC1 l r0 r1 d F d_o :  c_ineq bot3 (o r0) (o r1) d_o ->  (forall a, BuildCoerce ((r0,r1)::l) (a\r0) (a\r1) (F a)) ->
                                     d = (cfix (ctrans (decomp_l r0) 
                                               (ctrans (cplus d_o (sum_coerce F)) 
                                                       ((decomp_r r1)))))
                                         -> BuildCoerce l r0 r1 d
| BC2 d r0 r1 l : d = guard (var_dsl (index (r0,r1) l)) -> BuildCoerce l r0 r1 d
(*| BC3 c0 c1 d l  : c_ineq (BuildCoerce l) c0 c1 d ->   BuildCoerce l c0 c1 d.*)
| BC3 d d0 d1 c0 c0' c1 c1' l  : BuildCoerce l c0 c0' d0 -> BuildCoerce l c1 c1' d1 ->  d = cseq d0 d1 ->   BuildCoerce l (c0 _;_ c1) (c0' _;_ c1') d
| BC4 c0 c1 d l  : c_ineq bot3 c0 c1 d ->   BuildCoerce l c0 c1 d.




Lemma Build : forall c, { d| BuildCoerce nil  (Star (Star c))  (Star c) d}.
Proof.
intros. econ. 
apply: BC1. ssa.
intros. simpl.
apply: BC0. bt rule_assoc. lcid.
apply:BC3. apply:BC4. eauto.
apply:BC1. ssa. intros. simpl.
apply:BC0.  bt rule_untag. lcid.
apply:BC0. bt rule_assoc. lcid.
apply:BC3. apply:BC4. eauto.
apply:BC2. all:  done. 
Defined.


Lemma toBuildCoerce : forall c0 c1 l, IndContains l c0 c1 -> exists d, BuildCoerce l c0 c1 d.
Proof.
move=> c0 c1 l.
elim.
- intros. have: exists F : A -> dsl, forall e, BuildCoerce ((c2, c3) :: l0) (e \ c2) (e \ c3) (F e).
  clear H H1. 
  suff:  exists F : A -> dsl,
    forall e : A, e \in index_enum A ->  BuildCoerce ((c2, c3) :: l0) (e \ c2) (e \ c3) (F e).
  case. intros. exists x. intros. apply/p0. rewrite mem_index_enum //.
  move: (index_enum A)=> l'.
  elim : l'. exists (fun => cid). ssa.
  ssa. destruct (H0 a).
  exists (fun y => if y == a then x0 else x y). move=> e. rewrite !inE.
  destruct (eqVneq e a). subst. ssa. simpl. intros. eauto. 2:simpl.
  clear H0. case. intros. econ.
  apply:BC1.
  apply: nu_imp_coerce. done. apply:p0. done.
- intros. econ. apply:BC4. lct1. apply:H. lct2. apply:H0.
 eauto.
  intros. 
  

Lemma toBuildCoerce : forall c0 c1 l F, (forall x y, (x,y) \in l -> INEQ x y (F (x,y))) ->  IndContains l c0 c1 -> exists d, INEQ c0 c1 d.
Proof.
move=> c0 c1 /= l F Hl Hind /=.  
move: Hind Hl.
elim.
- intros. 
  have: exists F', forall e,
       (forall x y : regex, (x, y) \in (c2, c3) :: l0 -> x <C= y ~> F (x, y)) ->
         e \ c2 <C= e \ c3 ~> (F' e).
  suff: exists F', forall e, e \in index_enum A ->
       (forall x y : regex, (x, y) \in (c2, c3) :: l0 -> x <C= y ~> F (x, y)) ->
         e \ c2 <C= e \ c3 ~> (F' e).
  ssa. exists x. ssa. apply/H2. rewrite mem_index_enum //. eauto. 
  move: (index_enum A)=> l'.
  elim : l'. exists (fun => cid). ssa.
  ssa. destruct (H0 a). intros. destruct (orP H3);ssa. norm_eqs. inv H4.
  
  exists (fun x0 y => if y == a then x0 else x y). move=> e. rewrite !inE.
  destruct (eqVneq e a). subst. ssa. simpl. intros. eauto. 2:simpl.
  clear H0. case. intros. econ.
  pfold. lct1. apply:derive_unfold_coerce_l.
  lct2. apply:derive_unfold_coerce_r. 
  lcp1. apply/c_ineq_gen_mon. apply: nu_imp_coerce. done. done.
  apply:big_plus_coerce. intros. left. apply:p0. t0. t0. t0.
admit.

  have : exists F, forall e : A,  e \ c2 <C= e \ c3 ~> (F e).
  suff : exists F, forall e : A, e \in index_enum A ->   e \ c2 <C= e \ c3 ~> (F e).
  ssa. exists x. ssa. apply/H2. rewrite mem_index_enum //. 
  move: (index_enum A)=> l'.
  elim : l'. exists (fun => cid). ssa.
  ssa. destruct (H0 a). 
  exists (fun y => if y == a then x0 else x y). move=> e. rewrite !inE.
  destruct (eqVneq e a). subst. ssa. simpl. intros. eauto. 2:simpl.
  clear H0. case. intros. econ.
  pfold. lct1. apply:derive_unfold_coerce_l.
  lct2. apply:derive_unfold_coerce_r. 
  lcp1. apply/c_ineq_gen_mon. apply: nu_imp_coerce. done. done.
  apply:big_plus_coerce. intros. left. apply:p0. t0. t0. t0.
- intros. econ. pfold. lct1. apply:c_ineq_gen_mon. eauto. done. lct2. apply:c_ineq_gen_mon.  eauto. done.
  move: (Hl x y H1). sunfold. t0. t0.

intros.
intros.
 eauto.


  have : exists F', forall (e : A) (F : regex * regex -> dsl),
       (forall x y : regex, (x, y) \in (c2, c3) :: l0 -> x <C= y ~> F (x, y)) ->
        e \ c2 <C= e \ c3 ~> (F' e).
  suff : exists F', forall (e : A) (F : regex * regex -> dsl), e \in index_enum A ->
       (forall x y : regex, (x, y) \in (c2, c3) :: l0 -> x <C= y ~> F (x, y)) ->
        e \ c2 <C= e \ c3 ~> (F' e).
  ssa.  exists x. ssa. apply/H3. rewrite mem_index_enum //. eauto.
  move: (index_enum A)=> l'.
  elim : l'. exists (fun => cid). ssa.
  ssa. destruct (H0 a F). intros.  rewrite inE in H4. destruct (orP H4);ssa. norm_eqs. inv H5.
apply/H2.
  exists (fun y => if y == a then x0 else x y). move=> e. rewrite !inE.
  destruct (eqVneq e a). subst. ssa. simpl. intros. eauto. 2:simpl.
  clear H0. case. intros. econ.
  apply:BC1.
  apply: nu_imp_coerce. done. apply:p0. done.
- intros.
 eauto.







Lemma Build_type : forall c, Star (Star c) <C= Star c ~> (proj_sig (Build c)).
Proof.
intros.
move Heq: (proj_sig (Build _)) => d.
rewrite /=. pfold. rewrite -Heq /=. 
apply:rule_ctrans. rewrite /full_unf /=. done.

have :   (decomp_l (Star (Star c)))
  [d cfix
      (ctrans (decomp_l (Star (Star c)))
         (ctrans
            (cplus cid
               (sum_coerce
                  (fun=> ctrans
                           (ctrans assoc
                              (cseq cid
                                 (cfix
                                    (ctrans (decomp_l (Star c _;_ Star (Star c)))
                                       (ctrans
                                          (cplus cid
                                             (sum_coerce
                                                (fun=> ctrans
                                                         (ctrans untag
                                                            (ctrans
                                                               (ctrans assoc
                                                                  (cseq cid
                                                                    (guard
                                                                    (var_dsl (... ... ...)))))
                                                               cid)) cid))) 
                                          (decomp_r (Star c))))))) cid))) 
            (decomp_r (Star c)))) .: var_dsl] = (decomp_l (Star (Star c))).

(proj_sig (derive_unfold_coerce_l_aux bot3 (Star (Star c))))
  [d cfix
      (ctrans (proj_sig (derive_unfold_coerce_l_aux bot3 (Star (Star c))))
         (ctrans
            (cplus (nu_c (Star (Star c)) (Star c) ssrfun.id)
               (sum_coerce
                  (fun=> ctrans
                           (ctrans assoc
                              (cseq cid
                                 (cfix
                                    (ctrans
                                       (proj_sig
                                          (derive_unfold_coerce_l_aux bot3
                                             (Star c _;_ Star (Star c))))
                                       (ctrans
                                          (cplus
                                             (nu_c (Star c _;_ Star (Star c)) (Star c) ssrfun.id)
                                             (sum_coerce
                                                (fun=> ctrans
                                                         (ctrans untag
                                                            (ctrans
                                                               (ctrans assoc
                                                                  (cseq cid (guard (var_dsl 0))))
                                                               cid)) cid)))
                                          (antimorov_r (Star c))))))) cid)))
            (antimorov_r (Star c)))) .: var_dsl] = (proj_sig (derive_unfold_coerce_l_aux bot3 (Star (Star c)))) . admit.
move=>->.
Check derive_unfold_coerce_l.
apply: derive_unfold_coerce_l.

Parameter (a : A).
Eval compute in 


admit.
intros.  rewrite /ACI_l /=. rewrite /ACI_l_c_proof.
econ.
econ.
econ.
3 : { econ. } 
2: {  intros. econ.
ssa. rewrite /
3 : { intros. simpl. 
econ. econ.
intros. simpl. rewrite eqxx. done.

lcs1. lcid.
move=> a0. 
econ. intros. simpl.





Lemma my_test : forall c, { d| Star (Star c) <C= Star c ~> d}.
Proof.
intros. econ. move: c. pcofix CIH. intros.
pfold.
lct1. instantiate (1:= (cfix (ctrans untag
    (ctrans assoc
       (cseq cid
          (ctrans
             (proj_sig (derive_unfold_coerce_l_aux (upaco3 c_ineq r) (Star c _;_ Star (Star c))))
             (ctrans (cplus cid (\big[cplus/cid]_a1 guard (var_dsl 0)))
                (proj_sig (derive_unfold_coerce_r_aux (upaco3 c_ineq r) (Star c)))))))))). pfold_reverse. pfold.
 apply:derive_unfold_coerce_l. 
lct2. apply:derive_unfold_coerce_r. 
have: o (Star (Star c)) = Eps by done. move=>->.
have : o (Star c) = Eps. by done. move=>->.
lcp1. lcid. apply:big_plus_coerce. 
intros. simpl. left. simpl.  
pfold. 
lct1.  bt rule_assoc.
lcs1. lcid. pfold_reverse.
pfold.
lct1. apply:derive_unfold_coerce_l.
lct2. apply:derive_unfold_coerce_r.
lcp1. rewrite /o /=. eauto.
apply:big_plus_coerce. intros. left. move: a0 H0. pcofix CIH2. intros.
pfold. simpl.
lct1. bt rule_untag.
lct1.  bt rule_assoc.
lcs1. lcid.
lct1. apply:derive_unfold_coerce_l.
lct2. apply:derive_unfold_coerce_r.
lcp1. rewrite /o /=. eauto.
apply:big_plus_coerce. intros. right. 
apply: CIH2. done. t0. t0. t0.
all : try t0.

instantiate (2:= fun a => guard (var_dsl 0)).



 simpl. right.

Print c_ineq.

right. simpl.
rewrite /o. Check 
rewrite [nu _]/= [match true with | _ => _ end]/=.
 simpl. rewrite /o. simpl. =.



| BC1 x y r0 r1 l d d' (H0 : ACI r0 x) (H1: ACI r1 y): index (r0,r1) l = n (x,y) \in l -> full_unf d = ctrans (ACI_l H0) (ctrans d' (ACI_r H1))  
                                                                 -> BuildCoerce l r0 r1 d.
Hint Constructors BuildCoerce.

Inductive BuildCoerce : seq (regex * regex * dsl) -> regex -> regex -> dsl -> Type := 
| BC0 l r0 r1 d F (H: nu r0 -> nu r1) :  (forall a, BuildCoerce ((r0,r1,d)::l) (a\r0) (a\r1) (F a))
                                     -> full_unf d = ctrans (antimorov_l r0) (ctrans (cplus (nu_c r0 r1 H) (sum_coerce F)) (antimorov_r r1))  
                                     -> BuildCoerce l r0 r1 d
| BC1 x y r0 r1 l d d' (H0 : ACI r0 x) (H1: ACI r1 y): (x,y,d') \in l -> full_unf d = ctrans (ACI_l H0) (ctrans d' (ACI_r H1))  
                                                                 -> BuildCoerce l r0 r1 d.
Hint Constructors BuildCoerce.

Lemma ToBuildCoerce : forall l r0 r1, IndContains l r0 r1 -> (forall x y, (x,y) \in l -> exists z, BuildCoerce nil x y z)  ->  exists l' d, BuildCoerce l' r0 r1 d.
Proof.
move=> l r0 r1.
elim.
- intros.





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
| shuffle => y


Lemma TypesP: forall s c, Match s c <-> Types s c.
Proof.
move => s c. split;first by elim;eauto.
elim;eauto.
move=> c0 s0 HM HM2. inv HM2.
inv H1. inv H1. con. done. done.
Qed.


Lemma c_eqc_gen_mon: monotone2 c_eqc. 
Proof.
unfold monotone2.
intros. induction IN; eauto. 
apply/c_fix. done. elim: H0 LE;eauto.
Qed.
Hint Resolve c_eqc_gen_mon : paco.











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
move=> r r' f Hf T. move Heq: (upTree_0size T) => n. move: Heq. suff: upTree_0size T <= n -> typing T (Star r) -> typing (cstar_i f T) (Star r').
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
(forall x y (d : dsl_co x y) T, upTree_0size (f _ _ d T) <= upTree_0size T) ->  upTree_0size (interp_aux d f T) <= upTree_0size T.
Proof.
move=> r r' d f T.
destruct T;ssa.
destruct d;ssa.

elim: d T=>//=;intros. case: T=>//. move=>u. simpl. destruct u;ssa.
simpl.
 elim=>//.
*)
(*Lemma interp_aux_ext : forall r0 r1 (d : dsl dsl_co r0 r1) (f f' : forall x y, dsl_co x y -> fType) n T, upTree_0size T < n ->
 ( forall T, upTree_0size T < n -> forall x y (d : dsl_co x y), f _ _ d = f' _ _ d) -> interp_aux d f T = interp_aux d f' T. 
Proof.
move=> r0 r1. elim=>//.
- move=> A0 B C d IH d0 IH2 f f' n T Hsize Hext.
  rewrite /= /ctrans_i /=. erewrite IH. 2 : eauto. apply/IH2.*)


(*Lemma interp_n_unf : forall i n r0 r1 (d : dsl_co r0 r1) T, upTree_0size T < n -> interp_n n d T = interp_n (i + n) d T. 
Proof.
elim=>//.
move=> n IH n0 r0 r1 d T Hsize /=. destruct d. 
destruct n0. move:(upTree_1size1 T). lia.
simpl. destruct d=>//.
rewrite /= /ctrans_i /=. rewrite -IH.
f_equal.
rewrite -IH.
f_equal. 
rewrite IH //=.
rewrite /interp_aux.
*)
Definition interp (r0 r1 : regex) (d : dsl_co r0 r1) : fType := fun T => interp_n (upTree_0size T) d T.

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
move=> T. move Heq: (upTree_0size T)=>n. move: Heq.
suff:  upTree_0size T <= n ->
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
move=> T. move Heq: (upTree_0size T)=>n. move: Heq.
suff:  upTree_0size T <= n ->
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
move=> T. move Heq: (upTree_0size T)=>n. move: Heq.
suff:  upTree_0size T <= n ->
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

Lemma interpP : forall r0 r1 (d : dsl_co r0 r1) T, upTree_0size T < n -> typing T r0 -> typing (interp_n n d T) r1. 


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
(*apply/rule_guard=>//. left. pcofix CIH. pfold*)  
apply/rule_cseq=>//. apply/rule_cid=>//. (*Don't use rule_guard yet*) (*apply/rule_guard=>//. left=>//. pfold.*)

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
apply/rule_guard=>//. right. apply/CIH.

apply/rule_ctrans=>//. apply/rule_assoc=>//.
apply/rule_guard=>//. right.  apply/CIH2.
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
apply/rule_guard. right. instantiate (1:= var_dsl 1). admit. 

apply/rule_ctrans. apply/rule_assoc.
apply/rule_guard. right. instantiate (1:= var_dsl 0).
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

















(*Lemma seq_der : forall r r' s, ACI (s \\ (r _;_ r')) \big[Plus/Empt]_( n < size s) (((take n s \\ r) _;_ r') _+_ (o(r) _;_ n
  ((s \\ r) _;_ r'  _+_ (o(r) _;_ a \ r')).*)


Fixpoint derive2 (e:A) (c:regex) : seq regex :=
match c with
| Eps => Empt::nil
| Empt => Empt::nil
| Event e' => if e' == e then Eps::nil else Empt::nil
| c0 _;_ c1 => if nu c0 then 
                (map  (fun x => x _;_ c1) (derive2 e c0))  ++
                (derive2 e c1)
              else  (derive2 e c1)
| c0 _+_ c1 => (derive2 e  c0) ++  (derive2 e c1)
| Star c => map (fun x => x _;_ Star c) (derive2 e c)
end.


Lemma enum_closed : forall r0 r1 r2 e, r1 \in regex_enum r0 -> r2 \in (derive2 e r1) -> r2 \in regex_enum r0.
Proof.
elim;ssa. rewrite inE in H. destruct (orP H). norm_eqs. ssa. rewrite inE in H0. norm_eqs. auto.
rewrite !inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite !inE in H0. norm_eqs. eauto.
norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.
 rewrite inE in H. destruct (orP H). norm_eqs. ssa. rewrite inE in H0. norm_eqs. auto.
rewrite !inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite !inE in H0. norm_eqs. eauto.
norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.
 rewrite inE in H. destruct (orP H). norm_eqs. ssa. 
destruct (eqVneq s e). subst. rewrite inE in H0. norm_eqs. eauto. rewrite inE in H0. norm_eqs. eauto.
rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite inE in H0. norm_eqs. 
rewrite eqxx. lia. rewrite inE in H2. norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.

rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite mem_cat in H2. destruct (orP H2).
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
apply: H. 2 : eauto. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
rewrite inE in H3. destruct (orP H3). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia.
rewrite inE in H4. destruct (orP H4). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia.
rewrite mem_cat in H5. destruct (orP H5). 
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
eauto.
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
- rewrite inE in H1. destruct (orP H1). norm_eqs. ssa.
destruct (nu _) eqn:Heqn. ssa. rewrite mem_cat in H2. destruct (orP H2). 
destruct (mapP H3). subst. right. apply/orP. right. apply/orP. right. 
rewrite mem_cat. apply/orP. left. apply/mapP. econ. 2:eauto. apply:H. apply:selfe. apply:H4.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto. clear H1.
rewrite inE in H3. destruct (orP H3). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H3.
rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H1.
rewrite mem_cat in H3. destruct (orP H3). destruct (mapP H1). subst.  
rewrite !inE. apply/orP. simpl in H2.
destruct (nu _) eqn:Heqn.
rewrite mem_cat in H2. destruct (orP H2). destruct (mapP H5). subst.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
apply/map_f. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto.
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right.
eauto.

- rewrite !inE in H0. destruct (orP H0). norm_eqs. ssa. destruct (mapP H1). subst. right.
apply/orP. right. apply/orP. right. apply/map_f. eauto.
destruct (orP H2). norm_eqs. ssa. 
rewrite !inE in H1. norm_eqs. rewrite eqxx. lia.
destruct (orP H3). norm_eqs. ssa. rewrite inE in H1. norm_eqs.
right. rewrite eqxx. lia. 
destruct (mapP H4). norm_eqs. 
ssa. destruct (nu _) eqn:Heqn. rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H6).
subst. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H6). subst. 
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H1). subst.
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
Qed.











rewrite inE in H2. destruct (orP H2). norm_eqs. ssa.
  right. rewrite mem_cat. apply/orP. left. apply/map_f.  right. apply/mapP. econ. 2:eauto. apply:H. 
destruct (mapP H3). subst. right. apply/orP. right. apply/orP. right. 
rewrite mem_cat. apply/orP. left. apply/mapP. econ. 2:eauto.  eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto. clear H1.
rewrite inE in H3. destruct (orP H3). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H3.
rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H1.
rewrite mem_cat in H3. destruct (orP H3). destruct (mapP H1). subst.  
rewrite !inE. apply/orP. simpl in H2.
destruct (nu _) eqn:Heqn.
rewrite mem_cat in H2. destruct (orP H2). destruct (mapP H5). subst.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
apply/map_f. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto.
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right.
eauto.

- rewrite !inE in H0. destruct (orP H0). norm_eqs. ssa. destruct (mapP H1). subst. right.
apply/orP. right. apply/orP. right. apply/map_f. eauto.
destruct (orP H2). norm_eqs. ssa. 
rewrite !inE in H1. norm_eqs. rewrite eqxx. lia.
destruct (orP H3). norm_eqs. ssa. rewrite inE in H1. norm_eqs.
right. rewrite eqxx. lia. 
destruct (mapP H4). norm_eqs. 
ssa. destruct (nu _) eqn:Heqn. rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H6).
subst. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H6). subst. 
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H1). subst.
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
Qed.











apply/orP. right. apply/orP. right. apply/orP. right. 
  rewrite mem_cat. apply/orP. left. apply/mapP. econ.
rewrite inE in H1. destruct (orP H1). norm_eqs. ssa.
destruct (nu _) eqn:Heqn. ssa. 

rewrite mem_cat in H2. destruct (orP H2). 
destruct (mapP H3). subst. right. apply/orP. right. apply/orP. right. 
rewrite mem_cat. apply/orP. left. apply/mapP. econ. 2:eauto.  eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto. clear H1.
rewrite inE in H3. destruct (orP H3). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H3.
rewrite inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia. clear H1.
rewrite mem_cat in H3. destruct (orP H3). destruct (mapP H1). subst.  
rewrite !inE. apply/orP. simpl in H2.
destruct (nu _) eqn:Heqn.
rewrite mem_cat in H2. destruct (orP H2). destruct (mapP H5). subst.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. left.
apply/map_f. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right. eauto.
right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. eauto.
rewrite !inE. apply/orP. right. apply/orP. right. apply/orP. right. rewrite mem_cat. apply/orP. right.
eauto.

- rewrite !inE in H0. destruct (orP H0). norm_eqs. ssa. destruct (mapP H1). subst. right.
apply/orP. right. apply/orP. right. apply/map_f. eauto.
destruct (orP H2). norm_eqs. ssa. 
rewrite !inE in H1. norm_eqs. rewrite eqxx. lia.
destruct (orP H3). norm_eqs. ssa. rewrite inE in H1. norm_eqs.
right. rewrite eqxx. lia. 
destruct (mapP H4). norm_eqs. 
ssa. destruct (nu _) eqn:Heqn. rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H6).
subst. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H6). subst. 
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
destruct (mapP H1). subst.
apply/orP. apply/orP. right. apply/orP. right. apply/orP. right.
apply/map_f. eauto.
Qed.

Lemma derive_eq : forall r e, ACI (derive e r) (\big[Plus/Empt]_(r0 <- (derive2 e r)) r0).
Proof.
intros.

apply/mapP. econ. eauto.

right.
apply/orP. right. apply/orP. right.
rewrite mem_cat. apply/orP.  right.  bapply/mapP. econ.
apply/orP. right. apply/orP.  eauto. right. apply/H0. 2: eauto.
rewrite !inE in H3. destruct (orP H3). norm_eqs. ssa. rewrite inE in H2. norm_eqs. rewrite eqxx. lia.

rewrite inE in H1. destruct 


destruct (_==_) eqn:Heqn.  rewrite inE in H0. norm_eqs. auto.
rewrite !inE in H1. destruct (orP H1). norm_eqs. ssa. rewrite !inE in H0. norm_eqs. eauto.
norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto.
destruct (orP H). norm_eqs. ssa. rewrite inE in H0.
destruct (orP H). norm_eqs. ssa. rewrite inE in H0.
destruct (orP H). norm_eqs. ssa. rewrite inE in H0. norm_eqs. eauto. 

rewrite (eqP H) in H0. ssa. rewrite inE in H0.  

Fixpoint trace_derive2 (s : trace) (c : regex)  : seq regex :=
match s with
| [::] => c::nil
| e::s' => flatten (map (trace_derive2 s') (derive2 e c))
end.

Lemma regex_enumP : forall r, exists (l : seq regex), forall s, exists r', r' \in l /\ ACI (trace_derive s r) r'.

Fixpoint reg_size r := 
match r with 
| Eps => 0
| Empt => 0 
| Event _ => 1
| Plus r0 r1 => ((reg_size r0) + (reg_size r1)).+1
| Seq r0 r1 => ((reg_size r0) + (reg_size r1)).+1
| Star r0 => (reg_size r0).+1
end.
Lemma trace_derive_eq : forall a s r, trace_derive (a::s) r = (trace_derive s  (a\r)). 
Proof. done.
Qed.



Inductive seq_derive : trace -> seq (regex * regex) -> regex -> regex -> Prop := 
| sd0 r r' : seq_derive nil ((r,r')::nil) r r'
| sd1 r r' : nu r ->  seq_derive (a::s) l r r'


Lemma regex_enumP : forall r, exists (l : seq regex), forall s, exists r', r' \in l /\ ACI (trace_derive s r) r'.
Proof.
elim;ssa. exists (Eps::Empt::nil). elim;ssa. econ.  con. done. done. exists Empt. rewrite !inE orbC //=. ssa.
clear H H0. elim:l;ssa.
admit. admit.
exists (compose x0 x Plus). intros.
move: (H s) (H0 s). case. 
move=> x1 [] Hin1 HACI1.
move=>[] x2[] Hin2 HACI2. 

rewrite derive_distr_plus. econ. con. apply/mem_compose. eauto. eauto.
apply:ACI_p. done. done.
exists ((compose x0 x Seq)++(compose (compose x0 x Seq) x Plus)).
elim. simpl.
move: (H nil) (H0 nil). ssa. exists (Seq x2 x1). con. rewrite mem_cat. apply/orP. left.
apply/mem_compose. done. done. eauto.
intros. destruct H1. destruct H1. 
simpl.
destruct (nu _) eqn:Heqn. simpl.
rewrite derive_distr_plus. 
econ. con. 
2: { apply:ACI_p. apply:ACI_r. apply:ACI_r. } 
rewrite mem_cat. apply/orP. right.
apply/mem_compose. 
rewrite -!trace_derive_eq.

destruct (mem_compose H1).
econ. con.
 apply:mem_compose. 
destruct s. admit.
simpl.

con. <bintros. exists Eps. elim:s;ssa. 
econ. intros. 
Inductive Chain : seq regex -> regex -> Prop := 
| C0 l r : (forall a, Chain (r::l) (a \ r)) -> Chain l r
| C1 l r' r : r' \in l -> ACI r' r -> Chain l r.
Hint Constructors Chain.



(*Lemma reg_size_derive : forall r r', 0 < reg_size r -> reg_size (a \ r)*)

Lemma ChainP : forall r,  Chain l r.
Proof.
move=> r. move Heq: (reg_size r)=>n.
move: Heq. wlog: n r / reg_size r <= n. intros. apply/H. 2: eauto. lia.
move=>+_.
elim: n r.
- intros. destruct r0;ssa.
  con. intros. simpl. con. intros. simpl. apply:C1. done. done. 
  con. intros. simpl. apply:C1. done. done. 

- intros. destruct r0;ssa.
 * con. intros. simpl. case Heq: (_==_). rewrite (eqP Heq).
   con. intros. simpl. con. intros. simpl. econstructor 2. done. done.
   con. intros. econstructor 2. done. done.
 * 
- intros. con. intros. simpl. econstructor. intros.


Lemma ToIndContains : forall r0 r1 l, Contains r0 r1 -> IndContains l r0 r1.
Proof.





















Section Inductive_Equivalence.
Reserved Notation "l |- c0 =R= c1" (at level 63).


(*Maybe c_star_ctx and c_star_plus are not necessary*)

Inductive c_ind_eq : seq (regex * regex) -> regex -> regex -> Prop :=
| c_ind_plus_assoc l c0 c1 c2 : l |- (c0 _+_ c1) _+_ c2 =R= c0 _+_ (c1 _+_ c2)

| c_ind_plus_comm c0 c1 l:  l |- c0 _+_ c1 =R= c1 _+_ c0
| c_ind_plus_neut c l:  l |- c _+_ Empt =R= c
| c_ind_plus_idemp c l : l |- c _+_ c =R= c 
| c_ind_seq_assoc c0 c1 c2 l :  l |- (c0 _;_ c1) _;_ c2 =R= c0 _;_ (c1 _;_ c2)
| c_ind_seq_neut_l c l :  l |- (Eps _;_ c) =R= c 
| c_ind_seq_neut_r c l :  l |- c _;_ Eps =R= c 
| c_ind_seq_failure_l c l : l |- Empt _;_ c =R= Empt  
| c_ind_seq_failure_r c l :  l |-  c _;_ Empt =R= Empt 
| c_ind_distr_l c0 c1 c2 l : l |- c0 _;_ (c1 _+_ c2) =R= (c0 _;_ c1) _+_ (c0 _;_ c2)
| c_ind_distr_r c0 c1 c2 l : l |- (c0 _+_ c1) _;_ c2 =R= (c0 _;_ c2) _+_ (c1 _;_ c2)

| c_ind_unfold c l : l |-  Eps _+_ (c _;_ Star c) =R= Star c (*New star rule 1*)
| c_ind_star_plus c l :  l |-  Star (Eps _+_ c) =R= Star c (*New star rule 2*)
| c_ind_refl c l :  l |- c =R= c
| c_ind_sym c0 c1 l (H:  (c1,c0)::l |- c0 =R=c1) :  l |- c1 =R=c0
| c_ind_trans c0 c1 c2 l (H1 : (c0,c1)::l |- c0 =R=c1) (H2 :  (c0,c1)::l |- c1 =R=c2) :  l |- c0 =R=c2
| c_ind_plus_ctx c0 c0' c1 c1' l (H1 :  (c0 _+_ c1, c0' _+_ c1')::l |- c0 =R=c0') (H2 :  (c0 _+_ c1, c0' _+_ c1')::l |- c1 =R=c1') : l |- c0 _+_ c1 =R=c0' _+_ c1'
| c_ind_seq_ctx c0 c0' c1 c1' l (H1 :  (c0 _;_ c1,c0' _;_ c1')::l |- c0 =R=c0') (H2 :  (c0 _;_ c1,c0' _;_ c1')::l |- c1 =R=c1') :  l |- c0 _;_ c1 =R=c0' _;_ c1'
| c_ind_star_ctx c0 c1 l (H :  (Star c0,Star c1)::l |- c0 =R=c1) : l |- Star c0 =R= Star c1  (*new context rule*) 
| c_ind_guard a c0 c1 l : (Event a _;_ c0 , Event a _;_ c1)::l |-  c0 =R= c1 ->   l |- Event a _;_ c0 =R= Event a _;_ c1
| c_ind_l a c0 c1 l : (c0, c1) \in l ->   l |- Event a _;_ c0 =R= Event a _;_ c1
 where " l |- c1 =R= c2" := (c_ind_eq l c1 c2).
End Inductive_Equivalence.
Hint Constructors c_ind_eq.


Notation " l |- c0 =R= c1" := (c_ind_eq l c0 c1)(at level 63).
Definition IEQ l c0 c1 :=c_ind_eq l c0 c1.


Print INEQ.
Lemma EQ_coerce : forall l c0 c1 (R : regex -> regex -> dsl -> Prop), (forall x0 x1, (x0,x1) \in l -> exists d, R x0 x1 d) -> IEQ l c0 c1 -> exists d, (upaco3 c_ineq R c0 c1) d.
Proof. simpl.
move=> l c0 c1 R Hl HQ.
move: HQ Hl. elim.
- intros. exists shuffle. eauto.
  admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.
- intros. admit.
- intros.
edestruct H0. intros.
  rewrite inE in H1. destruct (orP H1). move/eqP: H2. case. intros;subst. admit.
econ. left. pfold. con. done.

Lemma Contains_INEQ : forall c0 c1, Bisimilarity c0 c1 -> c0 =C= c1.
Proof.
pcofix CIH.
intros. punfold H0. inversion H0.
pfold. rewrite (derive_unfold _ c0) (derive_unfold _ c1). subst.
rewrite /o H2.
suff:    \big[Plus/Empt]_a (Event a _;_ a \ c0) = (upaco2 c_eqc r)=
  \big[Plus/Empt]_a (Event a _;_ a \ c1). move=> HH.
 case Hcase:(nu _)=>//. eq_m_left. eq_m_left.
rewrite !big_shape.
move: (index_enum _)=>ef. elim: ef=>//.
move=> a l HQ/=. rewrite !big_cons. apply/c_plus_ctx=>//.
apply/c_fix=>/=. right. apply/CIH. case: (H1 a)=>//.
Qed.




(*Theorem equiv_r2 : forall c0 c1, Contains c0 c1 -> equiv_r c0 c1. 
Proof.
move=> c0 c1 HC s. 
elim: s c0 c1 HC.
- move=> c0 c1. sunfold. case. move=> ce c3 HC HC'. rewrite !matchbP /matchb /= HC' //.
- move=> a l IH c0 c1. sunfold. elim.
  move=> c2 c3 /(_ a) [] // HC _. rewrite !deriveP. apply/IH=>//.
Qed.*)















(*Lemma c_eqc_nu : forall R (c0 c1 : regex) , c0 =(R)= c1 -> nu c0 = nu c1.
Proof. 
intros. induction H; simpl; auto with bool; try btauto.
all : try (rewrite IHc_eqc1; rewrite IHc_eq; auto).
(*clear H.
elim: H0=>//. move=> x y l l' R' Hfor IH.
rewrite !big_cons //=.*)
Qed.*)

(*Lemma co_eq_nu : forall (c0 c1 : regex) , c0 =C= c1 -> nu c0 = nu c1.
Proof. 
intros. eapply c_eqc_nu. punfold H.
Qed.*)

Lemma c_plus_neut_l : forall R c, Empt _+_ c <R= c.
Proof. intros. rewrite c_plus_comm. auto.
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



Lemma seq_comm_o : forall R c c', c _;_ (o c') =(R)= (o c') _;_ c.
Proof.
move=> R c c'. rewrite /o. case Hcase: (nu _)=>//; rewrite !eqs_aux //.
Qed.


Let eqs :=   (eqs_aux,o_plus,o_seq).



Ltac eq_m_left := repeat rewrite c_plus_assoc; apply c_plus_ctx;
                  auto.

Ltac eq_m_right := repeat rewrite <- c_plus_assoc; apply c_plus_ctx;
                  auto.




(*Theorem equivP : forall c0 c1, equiv_r c0 c1 <-> Bisimilarity c0 c1.
Proof.
move=> c0 c1. con. apply/equiv_r1. apply/equiv_r2.
Qed.

Lemma bisim_soundness : forall (c0 c1 : regex), c0 =C= c1 -> Bisimilarity c0 c1.
Proof.
pcofix CIH. 
intros. pfold. constructor.
- intros. right. apply CIH.  apply co_eq_derive. auto.
- auto using co_eq_nu.
Qed.*)



(*Let o_eqs := (o_plus,o_seq,o_true,o_false).*)

Definition ex_eq {A : eqType} (l: seq A) (F0 F1 : A -> regex) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus : forall (l : seq A) F1 F2 (R: regex -> regex -> Prop), ex_eq l F1 F2 (c_eqc R) ->
   \big[Plus/Empt]_(i <- l) F1 i =( R )= \big[Plus/Empt]_(i <- l) F2 i.
Proof.
move=> + F1 F2 R. 
rewrite /ex_eq. elim=>//.
move=> _. rewrite !big_nil//.
move=> a l IH Hin. rewrite !big_cons. rewrite Hin //. 
eq_m_left.
Qed.

(*Necessary to use ssreflect under for rewriting*)
Add Parametric Morphism R : (Under_rel regex (c_eqc R)) with
signature (c_eqc R ==> c_eqc R ==> flip impl) as under_c_eqc. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''. apply/c_trans.  eauto. apply/c_trans. eauto. apply/c_sym. eauto.
Qed.

Add Parametric Morphism R : (Under_rel regex (c_eqc R)) with
signature (c_eqc R ==> c_eqc R ==> impl) as under_c_eq. 
Proof.
move=> x y HC x0 y0 HC'. intro. move: H. rewrite UnderE. move=> HC''.  apply/c_trans;last by eauto. apply/c_trans;last by eauto. apply/c_sym. eauto.
Qed.

(*This has to be proved by induction because I cannot use ssreflects big_split since commutativity is over c_eqc, and not leibniz equality*)
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
suff:    \big[Plus/Empt]_a (Event a _;_ a \ c0) = (upaco2 c_eqc r)=
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

Lemma INEQ_complete : forall c0 c1 d,(forall s, Match s c0 -> Match s c1) ->  INEQ c0 c1 d.






Lemma derive_unfold_coerce : forall R c,exists d, c_ineq R c (o c _+_ \big[Plus/Empt]_(a : A) (Event a _;_ a \ c)) d. 
Proof.
move=>R. 
elim;try solve [eauto].
- move=> s. rewrite /o/=. have: s \in index_enum A.  rewrite mem_index_enum //. move :( index_enum A)=> l.
  elim: l s. done. 
  move=> a l IH s. rewrite inE.  case: (eqVneq s a).   move=> Heq _.
  subst. rewrite big_cons eqxx. econ.
  lct2. lct2. bt rule_untagLinv. bt rule_tagL. t0. eauto. t0.
  move=>Heq /=. move/IH. case. intros. rewrite big_cons. rewrite (negbTE Heq).
  econ. lct2. bt rule_shuffle. 
  lct2. lcp1. bt rule_tagL. lcid. t0. eauto. t0. t0.
- move=> r0 [] x0 Heq0 r1 [] x1 Heq1. econ. 
  lct1. lcp1. apply:Heq0. apply:Heq1. t0.
  lct1. bt rule_shuffle. lct2. lcp1. apply: o_plus_r. lcid. t0.
  lct2. bt rule_shuffleinv. lcp1. lcid. 
  lct1. lct1. bt rule_retag. bt rule_shuffle. t0. 
  lcp1. lcid. simpl. 
  lct2. apply:eq_big_plus_c. intro. intros. bt rule_distLinv.
  lct2. lct2.  apply:split_plus_r.  bt rule_retag. t0.
  lcp1. lcid. lcid. t0. t0. 
  all: try t0.
- move=> r0 [] x0 Heq0 r1 [] x1 Heq1. econ.
  lct1. lcs1. apply: Heq0. apply: Heq1. t0.
  lct2. lcp1. apply: o_seq_r. lct2. apply: eq_big_plus_c.
  intro. intros. lct2. lcs1. lcid. apply: derive_seq_r. t0. lct2. bt rule_distLinv. 
  lcp2. lct2. lcs1. lcid.  apply:com_seq_o_r. t0. bt rule_assoc.  t0. bt rule_assoc. t0. t0. t0.
  lct2. apply: split_plus_r. lcp2. apply:factor_seq_r_r. apply:factor_seq_r_r. t0. t0. t0. t0.
  
lcid. t0. t0.
t0.
  lct2. lcp1. lcid. 
simpl.

lcid.
simpl. under eq_big_plus_c.
lct2. bt rule_shuffle.
apply:rule_ctrans. 2: { apply:rule_cplus. 2:eauto. 2:eauto. t0. } t0.
  apply:rule_ctrans. 3: {  apply:rule_cplus. 2: { apply:o_plus_r. } 
  2: {  apply:rule_cid. t0. }  t0. } 
  2: { apply:rule_ctrans. 2: {  apply:rule_shuffle. t0. } 
  2: { apply:rule_ctrans. 3: { apply:rule_shuffleinv. t0. } 
  2: { apply:rule_cplus. 2: { apply:rule_cid. t0. } 
  2: { apply:rule_ctrans. 2: bt rule_retag. 
  2: { apply:rule_ctrans. 2: bt rule_shuffle. 
  2: { apply:rule_cplus. 2: bt rule_cid.
  2: { simpl.

apply:rule_cplus. 2: { 

2: { 



econ. 2: { econ. instantiate (1:= untagLinv)=>//. }
  2: { econ.
move=>s.
  


under eq_big_plus. move=> a Hin. rewrite !eqs. over. rewrite plus_empt eqs //.
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
