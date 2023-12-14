

Section CoinductiveDSL.
Inductive dslF (R: regex -> regex -> Type) : regex -> regex -> Type := 
| co_shuffle A B C : dslF R ((A _+_ B) _+_ C) (A _+_ (B _+_ C))
| co_shuffleinv A B C : dslF R (A _+_ (B _+_ C)) ((A _+_ B) _+_ C)
| co_retag A B: dslF R (A _+_ B) (B _+_ A)
| co_untagL A : dslF R (Empt _+_ A) A
| co_untagLinv A: dslF R A  (Empt _+_ A)
| co_untag A : dslF R (A _+_ A)  A
| co_tagL A B : dslF R A  (A _+_ B )

| co_assoc A B C : dslF R ((A _;_ B) _;_ C)  (A _;_ (B _;_ C)) 
| co_associnv A B C : dslF R (A _;_ (B _;_ C))   ((A _;_ B) _;_ C)

| co_swap A :  dslF R (A _;_ Eps)  (Eps _;_ A) 
| co_swapinv A : dslF R(Eps _;_ A)  (A _;_ Eps) 

| co_proj A : dslF R (Eps _;_ A)  A 
| co_projinv A : dslF R A (Eps _;_ A) 

| co_abortR A : dslF R (A _;_ Empt)  Empt 
| co_abortRinv A : dslF R Empt   (A _;_ Empt) 

| co_abortL A : dslF R (Empt _;_ A)   Empt 
| co_abortLinv A : dslF R Empt    (Empt _;_ A)

| co_distL A B C : dslF R (A _;_ (B _+_ C))  ((A _;_ B) _+_ (A _;_ C))
| co_distLinv A B C : dslF R  ((A _;_ B) _+_ (A _;_ C)) (A _;_ (B _+_ C))

| co_distR A B C : dslF R ((A _+_ B) _;_ C)  ((A _;_ C) _+_ (B _;_ C))
| co_distRinv A B C : dslF R ((A _;_ C) _+_ (B _;_ C))   ((A _+_ B) _;_ C)

| co_wrap A : dslF R (Eps _+_ (A _;_ Star A))  (Star A)
| co_wrapinv A : dslF R (Star A)  (Eps _+_ (A _;_ Star A))

| co_drop A : dslF R  (Star (Eps _+_ A))  (Star A)
| co_dropinv A : dslF R (Star A)  (Star (Eps _+_ A))
| co_cid A : dslF R A A 

(*| ci_sym A B (H: A =R=B) : B =R=A*)
| co_ctrans A B C  : dslF R  A B ->  dslF R B C -> dslF R A C
| co_cplus A A' B B'  : dslF R A A'  -> dslF R B B' -> dslF R  (A _+_ B) (A' _+_ B')
| co_cseq A A' B B'  : dslF R A A' -> dslF R B B' ->  dslF R (A _;_ B) (A' _;_ B')
| co_cstar A B: dslF R  A B -> dslF R (Star A)  (Star B)
(*| cfix r r' (p  : dslF R dslF) : dslF R r  r' p[d (cfix p) .: dslF R var_dslF] ->  r  r' (cfix p) (*guarded p otherwise unsound*)*)
(*| guard a A B  : R A B -> dslF R ((Event a) _;_ A)  ((Event a) _;_ B)*)

(*We need this to be a sum because Coq disallows fix in cofix*)
| co_guard l (F F' : A -> regex)  : (forall a, R (F a) (F' a)) -> dslF R (\big[Plus/Empt]_(a <- l) ((Event a) _;_ F a))
                                                          (\big[Plus/Empt]_(a <- l) ((Event a) _;_ F' a)).
(**)

CoInductive dsl_co : regex -> regex -> Type := 
| Co_fold A B : (dslF dsl_co) A B -> dsl_co A B.
End CoinductiveDSL.
Arguments co_shuffle {R A B C}.
Arguments co_shuffleinv {R A B C}.
Arguments co_retag {R A B}.
Arguments co_untagL {R A}.
Arguments co_untagLinv {R A}.
Arguments co_untag {R A}.
Arguments co_tagL {R A B}.
Arguments co_assoc {R A B C}.
Arguments co_associnv {R A B C}.
Arguments co_swap {R A}.
Arguments co_swapinv {R A}.
Arguments co_proj {R A}.
Arguments co_projinv {R A}.
Arguments co_abortR {R A}.
Arguments co_abortRinv {R A}.
Arguments co_abortL {R A}.
Arguments co_abortLinv {R A}.
Arguments co_distL {R A B C}.
Arguments co_distLinv {R A B C}.
Arguments co_distR {R A B C}.
Arguments co_distRinv {R A B C}.
Arguments co_wrap {R A}.
Arguments co_wrapinv {R A}.
Arguments co_drop {R A}.
Arguments co_dropinv {R A}.
Arguments co_cid {R A}.
Arguments co_ctrans {R A B C}.
Arguments co_cplus {R A A' B B'}.
Arguments co_cseq {R A A' B B'}.
Arguments co_cstar {R A B}.
Hint Constructors dslF.
(*Arguments guard {R a A B}.*)

(*Arguments Co_build {A B}.*)

Section IndDSL_CoDSL.

Lemma dslF_plus_shape : forall a R x y, dslF R (\big[Plus/Empt]_(e <- a::nil) ((Event e) _;_ x))
                                    (\big[Plus/Empt]_(e <- a::nil) ((Event e) _;_ y)) -> dslF R (Event a _;_ x) 
                                                                                             (Event a _;_ y).
Proof.
intros. rewrite !big_cons !big_nil in X.
eauto.
Qed.

Definition fold_back : forall (r0 r1 : @regex A), dsl_co r0 r1 -> dslF dsl_co r0 r1.
Proof.
intros. inv X.
Defined.

(*Translation did not work*)

(*Definition coDSL_of l (r0 r1 : @regex A) (d : dsl l r0 r1) 
(f : forall (x y : @regex A) a, (x,y) \in l -> dslF dsl_co (Event a _;_ x) (Event a _;_ y)) : dslF dsl_co r0 r1.
elim: d f;ssa. 

admit. 
apply fold_back. cofix CIH.
con. apply X. 
intros.
rewrite !inE in H.
destruct (eqVneq (x,y) (A0,B)). case:e;intros. rewrite H0 H1.
apply dslF_plus_shape. 
apply co_guard. move=> _. apply CIH.  
clear CIH. ssa. Guarded.
apply:co_guard. move=>_. apply CIH. 
ssa. Guarded.
ssa.  move=> _. 
apply f.
move/eqP:Heqn. case. intros. subst. apply CIH. 
apply:f. simpl in H. apply H.
Qed.

con. apply:co_ctrans. apply/fold_back. apply/X. eauto. apply/fold_back. eauto.
con. apply:co_cplus. apply/fold_back. eauto. apply/fold_back. eauto.
con. apply:co_cseq. apply/fold_back. eauto. apply/fold_back. eauto.
con. apply:co_cstar. apply/fold_back. eauto. 
cofix CIH.
apply co_guard.
apply X. intros.  rewrite !inE in H. 
destruct ((x,y) == (A0,B)) eqn:Heqn.  con. apply:dslF_plus_shape.
move/eqP: Heqn. case. intros. subst. 
apply fold_back
apply Co_fold.
apply:co_guard. move=>_. apply CIH. 
ssa. Guarded.
ssa.  move=> _. 
apply f.
move/eqP:Heqn. case. intros. subst. apply CIH. 
apply:f. simpl in H. apply H.
Qed.
*)

