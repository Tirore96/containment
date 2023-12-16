

(*Arguments guard {R a A B}.*)

(*Arguments Co_build {A B}.*)

Section IndDSL_CoDSL.



(*
(*CoFixpoint dsl_co_mon R R' E F (d : dsl_co R E F) (fR : forall x y, R x y -> R' x y) :  dsl_co R' E F := 
match d with 
| Co_fold A B U => match U with 
                    | leftT d' => Co_fold lefT (dslF_mon d' fR)
                    | rightT R'*)


(* Preliminaries  *)

Section AND.

(* La conjonction dans le calcul minimal de 2nd ordre, selon Russell *)
  Variable p q : Prop.  

(* AND p q  proves any prop r which follows from p and q *)

  Definition AND := forall r : Prop, (p -> q -> r) -> r.  

(* Pairing, as conjunction introduction *)

  	Variable h1 : p.  
  	Variable h2 : q.  
  
		Theorem and : AND.
		Proof fun (r : Prop) (h : p -> q -> r) => h h1 h2.  

End AND.

Notation "A /\ B" := (AND A B) : type_scope.

(* Tarski's fixed-point theorem *)

Section Tarski.

(* All the hypotheses *)

  Variable A : Type.  
  Variable R : A -> A -> Prop.  
  Variable Rtrans : forall x y z : A, R x y -> R y z -> R x z.  
  Variable F : (A -> Prop) -> A.  
  Variable Upperb : forall (P : A -> Prop) (x : A), P x -> R x (F P).  
  Variable
    Least :
      forall (P : A -> Prop) (x : A),
      (forall y : A, P y -> R y x) -> R (F P) x.  
  Variable f : A -> A.  
  Variable Incr : forall x y : A, R x y -> R (f x) (f y).  

(* The construction of the proof *)

  Definition P0 (x : A) := R x (f x).  
  Definition x0 := F P0.  

(* the proof that x0 is a fixed point*)

Section lemme1.

  	Variable x : A.  
  	Variable h1 : R x (f x).  
  	Theorem lemme1 : R x (f x0).
          eauto.
        Qed.

End lemme1.
  
Lemma fact1 : R x0 (f x0).
eauto.
Qed.
  
Lemma fact2 : R (f x0) x0.
Proof. apply:Upperb. 
apply Incr. eauto.
Qed.

Theorem Tarski : R x0 (f x0) /\ R (f x0) x0.
Proof. apply and. eauto. apply fact2.
Qed.

End Tarski.

(* An application : Knaster-Tarski's theorem *)

Section Knaster.

  Variable U : Type.   
(* The current universe *)

  Definition set := U -> Type.  
  Definition Subset (x y : set) := forall u : U, x u -> y u.  
  Definition Equal (x y : set) := sumboolT (Subset x y)  (Subset y x).  
  Definition Class := set -> Prop.  
  Definition Map := set -> set.  
  Variable Phi : Map.  
  Variable Incr : forall x y : set, Subset x y -> Subset (Phi x) (Phi y).  
(* Here F will be union, defined as follows *)

(* (Over C x) iff x contains all the elements of all the sets in C *)
  Definition Over (C : Class) (x : set) := forall y : set, C y -> Subset y x.  
  Definition Union (C : Class) (u : U) := forall x : set, Over C x -> x u.  
(* Union has all the required properties *)

  Definition Subset_trans (x y z : set) (h1 : Subset x y) 
    (h2 : Subset y z) (u : U) (h3 : x u) := h2 u (h1 u h3).  
  Definition Union_upperb (C : Class) (x : set) (h1 : C x) 
    (u : U) (h2 : x u) (y : set) (h3 : Over C y) := 
    h3 x h1 u h2.  
  Definition Union_least (C : Class) (x : set)
    (h1 : forall y : set, C y -> Subset y x) (u : U) 
    (h2 : Union C u) := h2 x h1.  
(* We may now instantiate the general theorem *)

  Definition Stable (x : set) := Subset x (Phi x).  Check Stable.
  Definition S := Union Stable.  
Check (Phi S).
Lemma Knaster : Equal S (Phi S).
Proof Tarski set Subset Subset_trans Union Union_upperb Union_least Phi Incr.
							 
End Knaster.
*)

CoInductive rU_co {A B : Type} (R0 R1 : A -> B-> Type) : A -> B -> Type := 
 | U0 a b: R0 a b -> rU_co R0 R1 a b
 | U1 a b: R1 a b -> rU_co R0 R1 a b.


CoInductive Stream := 
| co_nil : Stream 
| co_cons : nat -> Stream -> Stream.

Variant eqF (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
 | NF0  :  eqF R co_nil co_nil
 | NF n l l' : R l l' -> eqF R (co_cons n l) (co_cons n l').

CoInductive co_test (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
| Co_test A B : (eqF (rU_co (co_test R) R)) A B -> co_test R A B.

Lemma eqF_mon : forall R R' E F, eqF R E F -> (forall x y, R x y -> R' x y) ->  eqF R' E F.
Proof.
intros. inv X. con. eauto. con. eauto.
Qed.

Lemma dsl_co_mon : forall R R' E F, co_test R E F -> (forall x y, R x y -> R' x y) ->  co_test R' E F.
Proof.
move=> R R'. 
cofix CIH.
intros. destruct X. destruct e. con.  con. destruct r. con. con. left. 
apply CIH. apply c. Guarded. apply X0.
con. con. right. apply X0. apply r.
Qed.

Definition singleton {A B : Type} (a : A) (b : B) := fun a0 b0 => a = a0 /\ b = b0.


Lemma accum1 : forall r0 r1 R,  co_test R r0 r1 -> co_test (rU R (singleton r0 r1)) r0 r1.
Proof.
intros. apply/dsl_co_mon. eauto. intros. left. done.
Qed.

Definition bot {A B : Type} := fun (_ : A) (_ : B) => False.
Definition top {A B : Type} := fun (_ : A) (_ : B) => True.

Lemma post_fix  : forall R a b, (forall x y, R x y -> eqF R x y) -> R a b -> co_test bot a b.
Proof.
move=> R. cofix CIH.
intros. apply X in X0. destruct X0. con. con.
con. con. left. apply CIH. apply X. apply r.
Qed.

Lemma post_fix2  : forall R R' a b, (forall x y, R x y -> eqF R x y) -> R a b -> co_test R' a b.
Proof.
intros. apply:dsl_co_mon. apply:post_fix. apply X. done. done.
Qed.

Lemma post_fix3  : forall R R' a b, (forall x y, R x y -> eqF (rU_co R' R) x y) -> R a b -> co_test R' a b.
Proof.
move=> R R'. cofix CIH.
intros. apply X in X0. destruct X0. con. con.
destruct r. con. con. right. apply r.
con. con. left. apply CIH. apply X. apply r.
Qed.

Lemma is_post  : forall R r0 r1 x y,  co_test (rU_co R (singleton r0 r1)) r0 r1 -> co_test (rU_co R (singleton r0 r1)) x y-> eqF (rU_co R (co_test (rU_co R (singleton r0 r1)))) x y.
Proof. 
move=> R r0 r1 x y Hr. intros.
destruct X. 
destruct e. con.
con. destruct r. right. done. destruct r. left. done.
destruct s. subst. right. done.
Qed.

Lemma accum2 : forall r0 r1 R, co_test (rU_co R (singleton r0 r1)) r0 r1 -> co_test R r0 r1.
Proof.
intros. eapply post_fix3. 2:apply:X. 
intros. apply:is_post. done. done.
Qed.

(*Inductive eqF2 (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
 | NF00  :  eqF2 R co_nil co_nil
 | NF11 n l l' : R l l' -> eqF2 R (co_cons n l) (co_cons n l')
 | NF22 n l l' : eqF2 R l l' -> eqF2 R (co_cons n l) l'.
Check eqF2_ind.
*)

CoInductive eqFF (R R': Stream -> Stream -> Type) : Stream -> Stream -> Type := 
 | NF00  :  eqFF R R' co_nil co_nil
 | NF11 n l l' : R' l l' -> eqFF R R' (co_cons n l) (co_cons n l')
 | FF n l l' : R l l' -> eqFF R R' (co_cons n l) l'.




Inductive eqF2 (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
 | EQF2 l l': eqFF (eqF2 R) R l l'   ->   eqF2 R l l'.

Lemma eqF2_ind2
     : forall (R : Stream -> Stream -> Type)  (P : forall s s0 : Stream, eqF2 R s s0 -> Type),
       (P co_nil co_nil (@EQF2 _ _ _ (@NF00 _ _))) ->
       (forall (n : nat) (l l' : Stream) (r : R l l'), P (co_cons n l) (co_cons n l') (@EQF2 _ _ _ (@NF11 _ _ _ _ _ r ))) ->
       (forall (n : nat) (l l' : Stream) (e : eqF2 R l l'), P l l' e -> P (co_cons n l) l' (@EQF2 _ _ _ (@FF _ _ _ _ _ e))) ->
       forall (s s0 : Stream) (e : eqF2 R s s0), P s s0 e.
Proof.
intros. move: s s0 e. fix IH 3.
intros. destruct e. destruct e. apply X.
apply X0. apply X1. apply IH.
Qed.

(*Lemma eqF2_ind2
     : forall (R : Stream -> Stream -> Type) (P : forall s s0, eqF2 R s s0 -> Type),
       (P co_nil co_nil (EQF2 (NF00 _ _))) ->
(*       (forall n (l l' : Stream) r, P l l' (EQF2 (@NF11 R n l l' r))) ->*)
       (forall n (l l' : Stream) r (e : eqFF (eqF2 R) R l l'), P l l' r -> P (co_cons n l) l' (EQF2 (FF r))) ->
       forall (s s0 : Stream) (e : eqF2 R s s0), P s s0 e.*)

CoInductive co_test2 (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
| Co_test2 A B : (eqF2 (rU_co (co_test2 R) R)) A B -> co_test2 R A B.


Lemma co_test_build2 : forall R R' l l',  eqF2 (rU_co (co_test2 R) R) l l'  -> (forall x y, R x y -> R' x y) -> 
 eqF2 (rU_co (co_test2 R) R') l l'.
Proof. 
move=> R R' + + + HR. 

move Heq: (fun l l' (H: eqF2 (rU_co (co_test2 R) R) l l') => eqF2 (rU_co (co_test2 R) R') l l') => P.
intros.
move: (@eqF2_ind2(rU_co (co_test2 R) R) P). subst.
move=> HH. apply HH. clear HH. all:eauto. con. con.

intros. con. con. destruct r. left. done. right. eauto.

intros.
con. con. done.
Qed.

Print co_test_build2.


(*Lemma co_test_build : forall R R' l l', co_test2 R l l' -> (forall x y, R x y -> R' x y) -> co_test2 R' l l'.
Proof.
cofix CIH.
intros. destruct X. destruct e. destruct e.
- con. con. con.
- destruct r. 
 * con. con. con. left. apply: CIH. apply c. apply X0. 
 * con. con. con. right. apply X0. apply r. 
 * con. con. con. destruct e. con.
apply:co_test_build2. apply e. done.*)
(*
Check eqF2_ind.

Lemma co_test_build : forall R R' l l', co_test2 R l l' -> (forall x y, R x y -> R' x y) -> co_test2 R' l l'.
Proof.
move => R R'. cofix CIH.
move=> l l' HC HR. destruct HC. elim:e. intros.
destruct e. 
- con. con. con.
- destruct r. 
 * con. con. con. left. apply CIH. apply c. apply X. 
 * con. con. con. right. apply X. apply r. 
 * con. con. con. destruct e. con. destruct e. con. con. 
   destruct r. con. apply CIH. apply c. done. Guarded.
   right. apply X. apply r. con.
destruct e. 
destruct e.
apply:co_test_build2. apply e. done.*)


(* | NF00  :  eqF2 R co_nil co_nil
 | NF11 n l l' : R l l' -> eqF2 R (co_cons n l) (co_cons n l')
 | NF22 n l l' : eqFF (eqF2 R) l l' -> eqF2 R (co_cons n l) l'.*)



Inductive eqF2 (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
 | NF00  :  eqF2 R co_nil co_nil
 | NF11 n l l' : R l l' -> eqF2 R (co_cons n l) (co_cons n l')
 | NF22 n l l' : eqF2 R l l' -> eqF2 R (co_cons n l) l'.


CoInductive co_test2 (R: Stream -> Stream -> Type) : Stream -> Stream -> Type := 
| Co_test2 A B : (eqF2 (rU_co (co_test2 R) R)) A B -> co_test2 R A B.

Lemma eqF_mon2 : forall R R' E F, eqF2 R E F -> (forall x y, R x y -> R' x y) ->  eqF2 R' E F.
Proof.
intros. induction X. con. con. eauto. con. done.
Qed.
Lemma dsl_co_mon2 : forall R R' E F, co_test2 R E F -> (forall x y, R x y -> R' x y) ->  co_test2 R' E F.
Proof.
move=> R R'. cofix CIH. intros.
destruct X. 
elim : e;intros. 
con.  con. 
destruct r. con. con. left. apply CIH. apply c. apply X0. 
con. con. right. apply X0. apply r. con. con. 
destruct X. done.
Qed.

Definition singleton {A B : Type} (a : A) (b : B) := fun a0 b0 => a = a0 /\ b = b0.


Lemma accum1 : forall r0 r1 R,  co_test R r0 r1 -> co_test (rU R (singleton r0 r1)) r0 r1.
Proof.
intros. apply/dsl_co_mon. eauto. intros. left. done.
Qed.

Definition bot {A B : Type} := fun (_ : A) (_ : B) => False.
Definition top {A B : Type} := fun (_ : A) (_ : B) => True.

Lemma post_fix  : forall R a b, (forall x y, R x y -> eqF R x y) -> R a b -> co_test bot a b.
Proof.
move=> R. cofix CIH.
intros. apply X in X0. destruct X0. con. con.
con. con. left. apply CIH. apply X. apply r.
Qed.

Lemma post_fix2  : forall R R' a b, (forall x y, R x y -> eqF R x y) -> R a b -> co_test R' a b.
Proof.
intros. apply:dsl_co_mon. apply:post_fix. apply X. done. done.
Qed.

Lemma post_fix3  : forall R R' a b, (forall x y, R x y -> eqF (rU_co R' R) x y) -> R a b -> co_test R' a b.
Proof.
move=> R R'. cofix CIH.
intros. apply X in X0. destruct X0. con. con.
destruct r. con. con. right. apply r.
con. con. left. apply CIH. apply X. apply r.
Qed.

Lemma is_post  : forall R r0 r1 x y,  co_test (rU_co R (singleton r0 r1)) r0 r1 -> co_test (rU_co R (singleton r0 r1)) x y-> eqF (rU_co R (co_test (rU_co R (singleton r0 r1)))) x y.
Proof. 
move=> R r0 r1 x y Hr. intros.
destruct X. 
destruct e. con.
con. destruct r. right. done. destruct r. left. done.
destruct s. subst. right. done.
Qed.

Lemma accum2 : forall r0 r1 R, co_test (rU_co R (singleton r0 r1)) r0 r1 -> co_test R r0 r1.
Proof.
intros. eapply post_fix3. 2:apply:X. 
intros. apply:is_post. done. done.
Qed.












Lemma co_principle : forall R l0 l1, (forall x y, R x y -> co_test R l0 l1) -> co_test R l0 l1.
Proof.
Admitted.


 con. con.

 destruct e. con. con.
inv X. inv X0. ssa.
cofix CIH. apply:dsl_co_mon. apply CIH. done. Qed.
con. con.
 apply:dsl_co_mon. apply X. *)

Definition uniqP {A B : Type} (P : A -> B -> Type)  := forall a b a' b', P a b -> P a' b' -> a = a' /\ b = b'.

Lemma my_cofix : forall R r0 r1, dsl_co (rU R (singleton r0 r1)) r0 r1 ->  dsl_co R r0 r1.
Proof. 
move=>  R r0 r1.
move Heq : (singleton _ _) => S.
move/[dup]. move=> HD HD'.
case: HD HD2.
remember r0. remember r1.
destruct HD.
have: dslF (rU (dsl_co (rU R (singleton r0 r1))) (R)) A0 B.
have: dslF (rU (dsl_co (rU R)) ( R)) A0 B.
apply/dslF_mon. apply d.
ssa.  destruct X. left. done. destruct r. right. rewrite /uniqP in Hun.
move: (@Hun _ _ _ _ p HP). ssa. subst. clear Hun.  
move: (@Hun _ _ p HP).
inv X0. left. done.  left. 
destruct X0. left. done. destruct r. left.  done. 
destruct s. subst. left. done.
right. done.
move=> X2.
eapply co_principle. 
intros. 
apply X2. apply X2.
Qed.
 con. con.
con.

Lemma my_cofix : forall (P : Stream -> Stream -> Type) R, ((forall r0 r1, P r0 r1 -> R r0 r1) -> forall r0 r1, co_test R r0 r1) -> forall r0 r1, P r0 r1 -> co_test R r0 r1.
Proof.
intros. move: (X r0 r1 X0).
  apply:dsl_co_mon. 

apply X.
apply X. intros.


Lemma eqF_mon : forall R R' E F, eqF R E F -> (forall x y, R x y -> R' x y) ->  eqF R' E F.
Proof.
intros. inv X. con. eauto.
Defined.
Lemma dsl_co_mon : forall R R' E F, dsl_co R E F -> (forall x y, R x y -> R' x y) ->  dsl_co R' E F.
Proof.
move=> R R'. 
cofix CIH.
intros. destruct X. con. apply:dslF_mon. apply d.
intros. destruct X. left. apply CIH. apply d0. 
E F d. destruct d.
elim: d R';try solve [ intros;con;auto with dsl].  
intros. con. apply:co_ctrans. apply:fold_back. eauto. apply:fold_back. eauto.
intros. con. apply:co_cplus. apply:fold_back. eauto. apply:fold_back. eauto.
intros. con. apply:co_cseq. apply:fold_back. eauto. apply:fold_back. eauto.
intros. con. apply:co_cstar. apply:fold_back. eauto. 

intros. con. apply:co_guard. 
inv r. left. 2:{ right. apply X. done. }

Defined.


Lemma my_cofix : forall (P : regex -> regex -> Type) R, ((forall r0 r1, P r0 r1 -> R r0 r1) -> forall r0 r1, dsl_co R r0 r1) -> forall r0 r1, P r0 r1 -> dsl_co R r0 r1.
Proof.
intros.  apply X. intros.
con. 
cofix CIH. 

Definition coDSL_of l R (r0 r1 : @regex A) (d : dsl l r0 r1) 
(f : forall (x y : @regex A), (x,y) \in l -> R x y) : dsl_co R r0 r1.
elim: d f;ssa; try solve [con;auto].
(*con. apply:co_ctrans. apply/fold
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
Qed.*)
con.
apply:co_ctrans. apply/fold_back. apply/X. eauto. apply/fold_back. eauto.
con. apply:co_cplus. apply/fold_back. eauto. apply/fold_back. eauto.
con. apply:co_cseq. apply/fold_back. eauto. apply/fold_back. eauto.
con. apply:co_cstar. apply/fold_back. eauto. 
con. apply co_guard. right. eauto. 
cofix CIH. apply X.
intros. rewrite !inE in H.
destruct ((x,y) == (A0,B)) eqn:Heqn.  
move/eqP: Heqn. case. intros. subst. apply CIH.
simpl in H. apply f. apply H.
Qed.
ssa. Guarded.
ssa.  move=> _. 
apply f.
move/eqP:Heqn. case. intros. subst. apply CIH. 
apply:f. simpl in H. apply H.
Qed.
*)

Definition fold_back : forall R (r0 r1 : @regex A), (dsl_co R r0 r1) -> dslF (rU (dsl_co R) R) r0 r1.
Proof.
intros. inv X. 
Defined.

Lemma dslF_mon : forall R R' E F, dslF R E F -> (forall x y, R x y -> R' x y) ->  dslF R' E F.
Proof.
move=> R R' E F d.
elim: d R';auto with dsl;simpl;intros.
apply:co_ctrans. eauto. eauto.
Defined.
