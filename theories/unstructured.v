



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











(*
Definition ex_eq {A : eqType} (l: seq A) (F0 F1 : A -> regex) R  := forall a, a \in l -> R (F0 a) (F1 a).

Lemma eq_big_plus2 : forall (l : seq A) F1 F2 R, ex_eq l F1 F2 (c_eq R) ->
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



Lemma factor_seq_r2 : forall R (B: eqType) l (P: B -> regex) c,
\big[Plus/Empt]_(a <- l) (P a _;_ c) =⟨R⟩= (\big[Plus/Empt]_(a <- l) (P a)) _;_ c.
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
- rewrite /o /=. under eq_big_plus2. move=> a Hin. rewrite !eqs2. over. rewrite plus_empt2 eqs2 //.
- rewrite /o /=. under eq_big_plus2. move=> a Hin. rewrite !eqs2. over. rewrite plus_empt2 eqs2 //.
- move => s. rewrite big_event_in2 /o //= ?eqs2 // mem_index_enum //. 
- move=> r HQ r' HQ'. rewrite o_plus2 /=. 
  under eq_big_plus2. move=> a Hin. rewrite eqs2. over. 
  rewrite split_plus2. 
  apply/c2_trans. apply/c2_plus_ctx. apply: HQ. apply: HQ'. eq_m_left2.  
  rewrite c2_plus_comm. eq_m_left2.
- move=> r HQ r' HQ'. 
  under eq_big_plus2. move=> a Hin. 
  rewrite derive_seq2 !eqs2 -!c2_seq_assoc seq_comm_o2 (c2_seq_assoc _ (o r)).
  over.
  rewrite split_plus2 !factor_seq_l2 !factor_seq_r2  o_seq2. 
  apply/c2_trans. apply/c2_seq_ctx. apply: HQ. apply: HQ'.
  apply/c2_trans. 2 : {  apply/c2_plus_ctx. apply/c2_refl. apply/c2_plus_ctx. apply/c2_seq_ctx. apply/c2_refl.
                        apply/c2_sym. apply: HQ'. apply/c2_refl. }
  rewrite !eqs2. eq_m_left2. 
- move=> r HQ /=. 
  under eq_big_plus2. move=> a Hin. rewrite -c2_seq_assoc. rewrite {2}HQ. over.
  rewrite factor_seq_r2. rewrite {1}HQ.
  rewrite {1}star_o2.
  rewrite {1}star_o2. 
  rewrite c2_unfold. done.
 (*We need c_star_plus here*)
Qed.
*)






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
