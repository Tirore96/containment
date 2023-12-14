From mathcomp Require Import all_ssreflect.
Require Import Paco.paco.

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
Locate split.
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


Ltac split_and :=
  intros;
   repeat
    match goal with
    | H:is_true (_ && _) |- _ => destruct (andP H); clear H
    | H:_ && _ = true |- _ => destruct (andP H); clear H
    | H:_ /\ _ |- _ => destruct H
    | |- _ /\ _ => con
    | |- is_true (_ && _) => apply /andP ; con
    | H : ex _ |- _ => destruct H
    end; auto.


Notation eq_iff := Bool.eq_iff_eq_true.
Ltac ssa' := rewrite ?inE;simpl in *; split_and;try done.
Ltac ssa := rewrite ?inE;simpl in *; split_ando;try done.

Ltac ptac := 
(match goal with 
                   | [ H : is_true (_ \in (map _ _)) |- _ ] => move/mapP : H;case;intros;subst
                   | [ H : is_true (_ \in (flatten _)) |- _ ] => move/flattenP : H;case;intros;subst
                   | [ H : is_true (_ \in (filter _ _)) |- _ ] => move : H;rewrite mem_filter
                   | [ H : is_true (_ \in (mem ((filter _ _)))) |- _ ] => move : H;rewrite mem_filter
                  end);ssa.

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

Ltac sunfold := let H := fresh "_Hunf" in move => H;punfold H;move : H.
