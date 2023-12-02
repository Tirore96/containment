From mathcomp Require Import all_ssreflect zify.
Require Import Containment.dsl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Containment.utils.


(*Adapted from a development on session types*)
Fixpoint mu_height g :=
match g with
| cfix l => (mu_height l).+1
| _ => 0
end.

Definition unf g := if g is cfix g' then g' [d g .: var_dsl]  else g.
Definition full_unf g := (iter (mu_height g) unf g).


(*guarded in the sense that full_unf d <> cfix ... 
  It might still be a non-terminating program (cfix. shuffle (var 0))
*)
Fixpoint guarded (i : nat) d := 
match d with
| var_dsl j => j != i
| cfix d' => guarded i.+1 d'
| _ => true 
end. 
Print dsl.
Fixpoint contractive d := 
match d with
| cfix d' => (guarded 0 d') && (contractive d')
| ctrans d0 d1 => (contractive d0) && (contractive d1)
| cplus d0 d1 => (contractive d0) && (contractive d1)
| cseq d0 d1 => (contractive d0) && (contractive d1)
| cstar d0 => (contractive d0)
| guard d0 => (contractive d0)
| _ => true 
end. 





Lemma mu_height_ren : forall g sigma, mu_height g ⟨d sigma ⟩  = mu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.

Lemma mu_height_subst : forall g0 sigma, (forall n, ~~ guarded n g0 -> mu_height (sigma n) = 0) ->  mu_height (g0[d sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (mu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. simpl. 
simpl in HH. lia. 
simpl. f_equal. asimpl. apply H. case. done.  simpl. intros. asimpl. rewrite mu_height_ren. apply/H0. done. 
Qed.


Lemma mu_height_unf : forall g , guarded 0 g -> (mu_height g) = mu_height (g [d cfix g .: var_dsl]).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. destruct n. done. done. ssa. erewrite mu_height_subst. done. case. done. 
intros. simpl. asimpl. destruct n. lia.  simpl. done. 
Qed.

Lemma mu_height_unf2 : forall g sigma i, ~~ guarded i g -> (mu_height g) + mu_height (sigma i) = mu_height (g [d sigma]).
Proof. 
elim;rewrite //=;intros. have : n = i by lia.  intros. subst. lia. 
asimpl. erewrite <- H. 2 : { eauto. } simpl. asimpl. rewrite mu_height_ren. lia. 
Qed.


Lemma guarded_test : forall e sigma i,  ~~ guarded i e -> iter (mu_height e) unf e [d sigma ] = sigma i. 
Proof. 
elim;rewrite //=;intros. 
have : n = i. lia.  move=>->. done.  asimpl. rewrite -iterS iterSr. simpl. asimpl. erewrite H. 
2 : { eauto. } simpl. done. 
Qed.


(*Even non contractive terms have the property that full unfolding equals full unfolding plus 1. This is what we need in projection lemma
 so we don't have to derive contractiveness of e from projection derivation*)
Lemma full_unf_subst : forall e, full_unf (cfix e) = full_unf (e [d cfix e .: var_dsl]). 
Proof. 
intros. rewrite /full_unf. 
intros. simpl.  rewrite -iterS iterSr. simpl. 
destruct (guarded 0 e) eqn:Heqn.  rewrite mu_height_unf. done. done. 
 erewrite guarded_test.  2 : { lia. } 
simpl. 
erewrite <-mu_height_unf2. 2 : { lia.  } simpl. 
rewrite addnC.  
rewrite iterD. erewrite guarded_test. 2 : { lia.  } simpl. rewrite -iterS iterSr /=. 
erewrite guarded_test. 2 : { lia. } done. 
Qed.


Lemma full_unf2 : forall n e, full_unf (iter n unf e) = full_unf e. 
Proof. 
elim. done. 
intros. rewrite iterS. 
destruct (if (iter n unf e) is cfix _ then true else false) eqn:Heqn. 
destruct ((iter n unf e))eqn:Heqn2;try done. simpl. 
rewrite -(H e) Heqn2. rewrite full_unf_subst. done. 
have : unf (iter n unf e) = iter n unf e. destruct ((iter n unf e));try done. 
move=>->. rewrite H. done. 
Qed.

Lemma full_unf_idemp : idemp full_unf. 
Proof. 
intros. rewrite /idemp. intros. rewrite {2}/full_unf. rewrite full_unf2. done. 
Qed.
