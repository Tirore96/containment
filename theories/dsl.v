From mathcomp Require Import all_ssreflect zify.

Require Export Containment.unscoped.


Section dsl.
Inductive dsl  : Type :=
  | var_dsl : ( fin ) -> dsl 
  | shuffle : dsl 
  | shuffleinv : dsl 
  | retag : dsl 
  | untagL : dsl 
  | untagLinv : dsl 
  | untag : dsl 
  | tagL : dsl 
  | assoc : dsl 
  | associnv : dsl 
  | swap : dsl 
  | swapinv : dsl 
  | proj : dsl 
  | projinv : dsl 
  | abortR : dsl 
  | abortRinv : dsl 
  | abortL : dsl 
  | abortLinv : dsl 
  | distL : dsl 
  | distLinv : dsl 
  | distR : dsl 
  | distRinv : dsl 
  | wrap : dsl 
  | wrapinv : dsl 
  | drop : dsl 
  | dropinv : dsl 
  | cid : dsl 
  | ctrans : ( dsl   ) -> ( dsl   ) -> dsl 
  | cplus : ( dsl   ) -> ( dsl   ) -> dsl 
  | cseq : ( dsl   ) -> ( dsl   ) -> dsl 
  | cstar : ( dsl   ) -> dsl 
  | cfix : ( dsl   ) -> dsl 
  | guard : ( dsl   ) -> dsl .

Lemma congr_shuffle  : shuffle  = shuffle  .
Proof. congruence. Qed.

Lemma congr_shuffleinv  : shuffleinv  = shuffleinv  .
Proof. congruence. Qed.

Lemma congr_retag  : retag  = retag  .
Proof. congruence. Qed.

Lemma congr_untagL  : untagL  = untagL  .
Proof. congruence. Qed.

Lemma congr_untagLinv  : untagLinv  = untagLinv  .
Proof. congruence. Qed.

Lemma congr_untag  : untag  = untag  .
Proof. congruence. Qed.

Lemma congr_tagL  : tagL  = tagL  .
Proof. congruence. Qed.

Lemma congr_assoc  : assoc  = assoc  .
Proof. congruence. Qed.

Lemma congr_associnv  : associnv  = associnv  .
Proof. congruence. Qed.

Lemma congr_swap  : swap  = swap  .
Proof. congruence. Qed.

Lemma congr_swapinv  : swapinv  = swapinv  .
Proof. congruence. Qed.

Lemma congr_proj  : proj  = proj  .
Proof. congruence. Qed.

Lemma congr_projinv  : projinv  = projinv  .
Proof. congruence. Qed.

Lemma congr_abortR  : abortR  = abortR  .
Proof. congruence. Qed.

Lemma congr_abortRinv  : abortRinv  = abortRinv  .
Proof. congruence. Qed.

Lemma congr_abortL  : abortL  = abortL  .
Proof. congruence. Qed.

Lemma congr_abortLinv  : abortLinv  = abortLinv  .
Proof. congruence. Qed.

Lemma congr_distL  : distL  = distL  .
Proof. congruence. Qed.

Lemma congr_distLinv  : distLinv  = distLinv  .
Proof. congruence. Qed.

Lemma congr_distR  : distR  = distR  .
Proof. congruence. Qed.

Lemma congr_distRinv  : distRinv  = distRinv  .
Proof. congruence. Qed.

Lemma congr_wrap  : wrap  = wrap  .
Proof. congruence. Qed.

Lemma congr_wrapinv  : wrapinv  = wrapinv  .
Proof. congruence. Qed.

Lemma congr_drop  : drop  = drop  .
Proof. congruence. Qed.

Lemma congr_dropinv  : dropinv  = dropinv  .
Proof. congruence. Qed.

Lemma congr_cid  : cid  = cid  .
Proof. congruence. Qed.

Lemma congr_ctrans  { s0 : dsl   } { s1 : dsl   } { t0 : dsl   } { t1 : dsl   } (H1 : s0 = t0) (H2 : s1 = t1) : ctrans  s0 s1 = ctrans  t0 t1 .
Proof. congruence. Qed.

Lemma congr_cplus  { s0 : dsl   } { s1 : dsl   } { t0 : dsl   } { t1 : dsl   } (H1 : s0 = t0) (H2 : s1 = t1) : cplus  s0 s1 = cplus  t0 t1 .
Proof. congruence. Qed.

Lemma congr_cseq  { s0 : dsl   } { s1 : dsl   } { t0 : dsl   } { t1 : dsl   } (H1 : s0 = t0) (H2 : s1 = t1) : cseq  s0 s1 = cseq  t0 t1 .
Proof. congruence. Qed.

Lemma congr_cstar  { s0 : dsl   } { t0 : dsl   } (H1 : s0 = t0) : cstar  s0 = cstar  t0 .
Proof. congruence. Qed.

Lemma congr_cfix  { s0 : dsl   } { t0 : dsl   } (H1 : s0 = t0) : cfix  s0 = cfix  t0 .
Proof. congruence. Qed.

Lemma congr_guard  { s0 : dsl   } { t0 : dsl   } (H1 : s0 = t0) : guard  s0 = guard  t0 .
Proof. congruence. Qed.

Definition upRen_dsl_dsl   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_dsl   (xidsl : ( fin ) -> fin) (s : dsl ) : dsl  :=
    match s return dsl  with
    | var_dsl  s => (var_dsl ) (xidsl s)
    | shuffle   => shuffle 
    | shuffleinv   => shuffleinv 
    | retag   => retag 
    | untagL   => untagL 
    | untagLinv   => untagLinv 
    | untag   => untag 
    | tagL   => tagL 
    | assoc   => assoc 
    | associnv   => associnv 
    | swap   => swap 
    | swapinv   => swapinv 
    | proj   => proj 
    | projinv   => projinv 
    | abortR   => abortR 
    | abortRinv   => abortRinv 
    | abortL   => abortL 
    | abortLinv   => abortLinv 
    | distL   => distL 
    | distLinv   => distLinv 
    | distR   => distR 
    | distRinv   => distRinv 
    | wrap   => wrap 
    | wrapinv   => wrapinv 
    | drop   => drop 
    | dropinv   => dropinv 
    | cid   => cid 
    | ctrans  s0 s1 => ctrans  ((ren_dsl xidsl) s0) ((ren_dsl xidsl) s1)
    | cplus  s0 s1 => cplus  ((ren_dsl xidsl) s0) ((ren_dsl xidsl) s1)
    | cseq  s0 s1 => cseq  ((ren_dsl xidsl) s0) ((ren_dsl xidsl) s1)
    | cstar  s0 => cstar  ((ren_dsl xidsl) s0)
    | cfix  s0 => cfix  ((ren_dsl (upRen_dsl_dsl xidsl)) s0)
    | guard  s0 => guard  ((ren_dsl xidsl) s0)
    end.

Definition up_dsl_dsl   (sigma : ( fin ) -> dsl ) : ( fin ) -> dsl  :=
  (scons) ((var_dsl ) (var_zero)) ((funcomp) (ren_dsl (shift)) sigma).

Fixpoint subst_dsl   (sigmadsl : ( fin ) -> dsl ) (s : dsl ) : dsl  :=
    match s return dsl  with
    | var_dsl  s => sigmadsl s
    | shuffle   => shuffle 
    | shuffleinv   => shuffleinv 
    | retag   => retag 
    | untagL   => untagL 
    | untagLinv   => untagLinv 
    | untag   => untag 
    | tagL   => tagL 
    | assoc   => assoc 
    | associnv   => associnv 
    | swap   => swap 
    | swapinv   => swapinv 
    | proj   => proj 
    | projinv   => projinv 
    | abortR   => abortR 
    | abortRinv   => abortRinv 
    | abortL   => abortL 
    | abortLinv   => abortLinv 
    | distL   => distL 
    | distLinv   => distLinv 
    | distR   => distR 
    | distRinv   => distRinv 
    | wrap   => wrap 
    | wrapinv   => wrapinv 
    | drop   => drop 
    | dropinv   => dropinv 
    | cid   => cid 
    | ctrans  s0 s1 => ctrans  ((subst_dsl sigmadsl) s0) ((subst_dsl sigmadsl) s1)
    | cplus  s0 s1 => cplus  ((subst_dsl sigmadsl) s0) ((subst_dsl sigmadsl) s1)
    | cseq  s0 s1 => cseq  ((subst_dsl sigmadsl) s0) ((subst_dsl sigmadsl) s1)
    | cstar  s0 => cstar  ((subst_dsl sigmadsl) s0)
    | cfix  s0 => cfix  ((subst_dsl (up_dsl_dsl sigmadsl)) s0)
    | guard  s0 => guard  ((subst_dsl sigmadsl) s0)
    end.

Definition upId_dsl_dsl  (sigma : ( fin ) -> dsl ) (Eq : forall x, sigma x = (var_dsl ) x) : forall x, (up_dsl_dsl sigma) x = (var_dsl ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_dsl (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint idSubst_dsl  (sigmadsl : ( fin ) -> dsl ) (Eqdsl : forall x, sigmadsl x = (var_dsl ) x) (s : dsl ) : subst_dsl sigmadsl s = s :=
    match s return subst_dsl sigmadsl s = s with
    | var_dsl  s => Eqdsl s
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((idSubst_dsl sigmadsl Eqdsl) s0) ((idSubst_dsl sigmadsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((idSubst_dsl sigmadsl Eqdsl) s0) ((idSubst_dsl sigmadsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((idSubst_dsl sigmadsl Eqdsl) s0) ((idSubst_dsl sigmadsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((idSubst_dsl sigmadsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((idSubst_dsl (up_dsl_dsl sigmadsl) (upId_dsl_dsl (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((idSubst_dsl sigmadsl Eqdsl) s0)
    end.

Definition upExtRen_dsl_dsl   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_dsl_dsl xi) x = (upRen_dsl_dsl zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint extRen_dsl   (xidsl : ( fin ) -> fin) (zetadsl : ( fin ) -> fin) (Eqdsl : forall x, xidsl x = zetadsl x) (s : dsl ) : ren_dsl xidsl s = ren_dsl zetadsl s :=
    match s return ren_dsl xidsl s = ren_dsl zetadsl s with
    | var_dsl  s => (ap) (var_dsl ) (Eqdsl s)
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((extRen_dsl xidsl zetadsl Eqdsl) s0) ((extRen_dsl xidsl zetadsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((extRen_dsl xidsl zetadsl Eqdsl) s0) ((extRen_dsl xidsl zetadsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((extRen_dsl xidsl zetadsl Eqdsl) s0) ((extRen_dsl xidsl zetadsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((extRen_dsl xidsl zetadsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((extRen_dsl (upRen_dsl_dsl xidsl) (upRen_dsl_dsl zetadsl) (upExtRen_dsl_dsl (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((extRen_dsl xidsl zetadsl Eqdsl) s0)
    end.

Definition upExt_dsl_dsl   (sigma : ( fin ) -> dsl ) (tau : ( fin ) -> dsl ) (Eq : forall x, sigma x = tau x) : forall x, (up_dsl_dsl sigma) x = (up_dsl_dsl tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_dsl (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint ext_dsl   (sigmadsl : ( fin ) -> dsl ) (taudsl : ( fin ) -> dsl ) (Eqdsl : forall x, sigmadsl x = taudsl x) (s : dsl ) : subst_dsl sigmadsl s = subst_dsl taudsl s :=
    match s return subst_dsl sigmadsl s = subst_dsl taudsl s with
    | var_dsl  s => Eqdsl s
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((ext_dsl sigmadsl taudsl Eqdsl) s0) ((ext_dsl sigmadsl taudsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((ext_dsl sigmadsl taudsl Eqdsl) s0) ((ext_dsl sigmadsl taudsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((ext_dsl sigmadsl taudsl Eqdsl) s0) ((ext_dsl sigmadsl taudsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((ext_dsl sigmadsl taudsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((ext_dsl (up_dsl_dsl sigmadsl) (up_dsl_dsl taudsl) (upExt_dsl_dsl (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((ext_dsl sigmadsl taudsl Eqdsl) s0)
    end.

Definition up_ren_ren_dsl_dsl    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_dsl_dsl tau) (upRen_dsl_dsl xi)) x = (upRen_dsl_dsl theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_dsl    (xidsl : ( fin ) -> fin) (zetadsl : ( fin ) -> fin) (rhodsl : ( fin ) -> fin) (Eqdsl : forall x, ((funcomp) zetadsl xidsl) x = rhodsl x) (s : dsl ) : ren_dsl zetadsl (ren_dsl xidsl s) = ren_dsl rhodsl s :=
    match s return ren_dsl zetadsl (ren_dsl xidsl s) = ren_dsl rhodsl s with
    | var_dsl  s => (ap) (var_dsl ) (Eqdsl s)
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s0) ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s0) ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s0) ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((compRenRen_dsl (upRen_dsl_dsl xidsl) (upRen_dsl_dsl zetadsl) (upRen_dsl_dsl rhodsl) (up_ren_ren (_) (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((compRenRen_dsl xidsl zetadsl rhodsl Eqdsl) s0)
    end.

Definition up_ren_subst_dsl_dsl    (xi : ( fin ) -> fin) (tau : ( fin ) -> dsl ) (theta : ( fin ) -> dsl ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_dsl_dsl tau) (upRen_dsl_dsl xi)) x = (up_dsl_dsl theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_dsl (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint compRenSubst_dsl    (xidsl : ( fin ) -> fin) (taudsl : ( fin ) -> dsl ) (thetadsl : ( fin ) -> dsl ) (Eqdsl : forall x, ((funcomp) taudsl xidsl) x = thetadsl x) (s : dsl ) : subst_dsl taudsl (ren_dsl xidsl s) = subst_dsl thetadsl s :=
    match s return subst_dsl taudsl (ren_dsl xidsl s) = subst_dsl thetadsl s with
    | var_dsl  s => Eqdsl s
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s0) ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s0) ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s0) ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((compRenSubst_dsl (upRen_dsl_dsl xidsl) (up_dsl_dsl taudsl) (up_dsl_dsl thetadsl) (up_ren_subst_dsl_dsl (_) (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((compRenSubst_dsl xidsl taudsl thetadsl Eqdsl) s0)
    end.

Definition up_subst_ren_dsl_dsl    (sigma : ( fin ) -> dsl ) (zetadsl : ( fin ) -> fin) (theta : ( fin ) -> dsl ) (Eq : forall x, ((funcomp) (ren_dsl zetadsl) sigma) x = theta x) : forall x, ((funcomp) (ren_dsl (upRen_dsl_dsl zetadsl)) (up_dsl_dsl sigma)) x = (up_dsl_dsl theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_dsl (shift) (upRen_dsl_dsl zetadsl) ((funcomp) (shift) zetadsl) (fun x => Logic.eq_refl) (sigma fin_n)) ((eq_trans) ((Logic.eq_sym) (compRenRen_dsl zetadsl (shift) ((funcomp) (shift) zetadsl) (fun x => Logic.eq_refl) (sigma fin_n))) ((ap) (ren_dsl (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstRen_dsl    (sigmadsl : ( fin ) -> dsl ) (zetadsl : ( fin ) -> fin) (thetadsl : ( fin ) -> dsl ) (Eqdsl : forall x, ((funcomp) (ren_dsl zetadsl) sigmadsl) x = thetadsl x) (s : dsl ) : ren_dsl zetadsl (subst_dsl sigmadsl s) = subst_dsl thetadsl s :=
    match s return ren_dsl zetadsl (subst_dsl sigmadsl s) = subst_dsl thetadsl s with
    | var_dsl  s => Eqdsl s
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s0) ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s0) ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s0) ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((compSubstRen_dsl (up_dsl_dsl sigmadsl) (upRen_dsl_dsl zetadsl) (up_dsl_dsl thetadsl) (up_subst_ren_dsl_dsl (_) (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((compSubstRen_dsl sigmadsl zetadsl thetadsl Eqdsl) s0)
    end.

Definition up_subst_subst_dsl_dsl    (sigma : ( fin ) -> dsl ) (taudsl : ( fin ) -> dsl ) (theta : ( fin ) -> dsl ) (Eq : forall x, ((funcomp) (subst_dsl taudsl) sigma) x = theta x) : forall x, ((funcomp) (subst_dsl (up_dsl_dsl taudsl)) (up_dsl_dsl sigma)) x = (up_dsl_dsl theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_dsl (shift) (up_dsl_dsl taudsl) ((funcomp) (up_dsl_dsl taudsl) (shift)) (fun x => Logic.eq_refl) (sigma fin_n)) ((eq_trans) ((Logic.eq_sym) (compSubstRen_dsl taudsl (shift) ((funcomp) (ren_dsl (shift)) taudsl) (fun x => Logic.eq_refl) (sigma fin_n))) ((ap) (ren_dsl (shift)) (Eq fin_n)))
  | 0  => Logic.eq_refl
  end.

Fixpoint compSubstSubst_dsl    (sigmadsl : ( fin ) -> dsl ) (taudsl : ( fin ) -> dsl ) (thetadsl : ( fin ) -> dsl ) (Eqdsl : forall x, ((funcomp) (subst_dsl taudsl) sigmadsl) x = thetadsl x) (s : dsl ) : subst_dsl taudsl (subst_dsl sigmadsl s) = subst_dsl thetadsl s :=
    match s return subst_dsl taudsl (subst_dsl sigmadsl s) = subst_dsl thetadsl s with
    | var_dsl  s => Eqdsl s
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s0) ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s0) ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s0) ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((compSubstSubst_dsl (up_dsl_dsl sigmadsl) (up_dsl_dsl taudsl) (up_dsl_dsl thetadsl) (up_subst_subst_dsl_dsl (_) (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((compSubstSubst_dsl sigmadsl taudsl thetadsl Eqdsl) s0)
    end.

Definition rinstInst_up_dsl_dsl   (xi : ( fin ) -> fin) (sigma : ( fin ) -> dsl ) (Eq : forall x, ((funcomp) (var_dsl ) xi) x = sigma x) : forall x, ((funcomp) (var_dsl ) (upRen_dsl_dsl xi)) x = (up_dsl_dsl sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_dsl (shift)) (Eq fin_n)
  | 0  => Logic.eq_refl
  end.

Fixpoint rinst_inst_dsl   (xidsl : ( fin ) -> fin) (sigmadsl : ( fin ) -> dsl ) (Eqdsl : forall x, ((funcomp) (var_dsl ) xidsl) x = sigmadsl x) (s : dsl ) : ren_dsl xidsl s = subst_dsl sigmadsl s :=
    match s return ren_dsl xidsl s = subst_dsl sigmadsl s with
    | var_dsl  s => Eqdsl s
    | shuffle   => congr_shuffle 
    | shuffleinv   => congr_shuffleinv 
    | retag   => congr_retag 
    | untagL   => congr_untagL 
    | untagLinv   => congr_untagLinv 
    | untag   => congr_untag 
    | tagL   => congr_tagL 
    | assoc   => congr_assoc 
    | associnv   => congr_associnv 
    | swap   => congr_swap 
    | swapinv   => congr_swapinv 
    | proj   => congr_proj 
    | projinv   => congr_projinv 
    | abortR   => congr_abortR 
    | abortRinv   => congr_abortRinv 
    | abortL   => congr_abortL 
    | abortLinv   => congr_abortLinv 
    | distL   => congr_distL 
    | distLinv   => congr_distLinv 
    | distR   => congr_distR 
    | distRinv   => congr_distRinv 
    | wrap   => congr_wrap 
    | wrapinv   => congr_wrapinv 
    | drop   => congr_drop 
    | dropinv   => congr_dropinv 
    | cid   => congr_cid 
    | ctrans  s0 s1 => congr_ctrans ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s0) ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s1)
    | cplus  s0 s1 => congr_cplus ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s0) ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s1)
    | cseq  s0 s1 => congr_cseq ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s0) ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s1)
    | cstar  s0 => congr_cstar ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s0)
    | cfix  s0 => congr_cfix ((rinst_inst_dsl (upRen_dsl_dsl xidsl) (up_dsl_dsl sigmadsl) (rinstInst_up_dsl_dsl (_) (_) Eqdsl)) s0)
    | guard  s0 => congr_guard ((rinst_inst_dsl xidsl sigmadsl Eqdsl) s0)
    end.

Lemma rinstInst_dsl   (xidsl : ( fin ) -> fin) : ren_dsl xidsl = subst_dsl ((funcomp) (var_dsl ) xidsl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_dsl xidsl (_) (fun n => Logic.eq_refl) x)). Qed.

Lemma instId_dsl  : subst_dsl (var_dsl ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_dsl (var_dsl ) (fun n => Logic.eq_refl) ((id) x))). Qed.

Lemma rinstId_dsl  : @ren_dsl   (id) = id .
Proof. exact ((eq_trans) (rinstInst_dsl ((id) (_))) instId_dsl). Qed.

Lemma varL_dsl   (sigmadsl : ( fin ) -> dsl ) : (funcomp) (subst_dsl sigmadsl) (var_dsl ) = sigmadsl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma varLRen_dsl   (xidsl : ( fin ) -> fin) : (funcomp) (ren_dsl xidsl) (var_dsl ) = (funcomp) (var_dsl ) xidsl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => Logic.eq_refl)). Qed.

Lemma compComp_dsl    (sigmadsl : ( fin ) -> dsl ) (taudsl : ( fin ) -> dsl ) (s : dsl ) : subst_dsl taudsl (subst_dsl sigmadsl s) = subst_dsl ((funcomp) (subst_dsl taudsl) sigmadsl) s .
Proof. exact (compSubstSubst_dsl sigmadsl taudsl (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compComp'_dsl    (sigmadsl : ( fin ) -> dsl ) (taudsl : ( fin ) -> dsl ) : (funcomp) (subst_dsl taudsl) (subst_dsl sigmadsl) = subst_dsl ((funcomp) (subst_dsl taudsl) sigmadsl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_dsl sigmadsl taudsl n)). Qed.

Lemma compRen_dsl    (sigmadsl : ( fin ) -> dsl ) (zetadsl : ( fin ) -> fin) (s : dsl ) : ren_dsl zetadsl (subst_dsl sigmadsl s) = subst_dsl ((funcomp) (ren_dsl zetadsl) sigmadsl) s .
Proof. exact (compSubstRen_dsl sigmadsl zetadsl (_) (fun n => Logic.eq_refl) s). Qed.

Lemma compRen'_dsl    (sigmadsl : ( fin ) -> dsl ) (zetadsl : ( fin ) -> fin) : (funcomp) (ren_dsl zetadsl) (subst_dsl sigmadsl) = subst_dsl ((funcomp) (ren_dsl zetadsl) sigmadsl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_dsl sigmadsl zetadsl n)). Qed.

Lemma renComp_dsl    (xidsl : ( fin ) -> fin) (taudsl : ( fin ) -> dsl ) (s : dsl ) : subst_dsl taudsl (ren_dsl xidsl s) = subst_dsl ((funcomp) taudsl xidsl) s .
Proof. exact (compRenSubst_dsl xidsl taudsl (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renComp'_dsl    (xidsl : ( fin ) -> fin) (taudsl : ( fin ) -> dsl ) : (funcomp) (subst_dsl taudsl) (ren_dsl xidsl) = subst_dsl ((funcomp) taudsl xidsl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_dsl xidsl taudsl n)). Qed.

Lemma renRen_dsl    (xidsl : ( fin ) -> fin) (zetadsl : ( fin ) -> fin) (s : dsl ) : ren_dsl zetadsl (ren_dsl xidsl s) = ren_dsl ((funcomp) zetadsl xidsl) s .
Proof. exact (compRenRen_dsl xidsl zetadsl (_) (fun n => Logic.eq_refl) s). Qed.

Lemma renRen'_dsl    (xidsl : ( fin ) -> fin) (zetadsl : ( fin ) -> fin) : (funcomp) (ren_dsl zetadsl) (ren_dsl xidsl) = ren_dsl ((funcomp) zetadsl xidsl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_dsl xidsl zetadsl n)). Qed.

End dsl.




































































Global Instance Subst_dsl   : Subst1 (( fin ) -> dsl ) (dsl ) (dsl ) := @subst_dsl   .

Global Instance Ren_dsl   : Ren1 (( fin ) -> fin) (dsl ) (dsl ) := @ren_dsl   .

Global Instance VarInstance_dsl  : Var (fin) (dsl ) := @var_dsl  .

Notation "x '__dsl'" := (var_dsl x) (at level 5, format "x __dsl") : subst_scope.

Notation "x '__dsl'" := (@ids (_) (_) VarInstance_dsl x) (at level 5, only printing, format "x __dsl") : subst_scope.


Class Up_dsl X Y := up_dsl : ( X ) -> Y.

Notation "↑__dsl" := (up_dsl) (only printing) : subst_scope.

Notation "↑__dsl" := (up_dsl_dsl) (only printing) : subst_scope.

Global Instance Up_dsl_dsl   : Up_dsl (_) (_) := @up_dsl_dsl   .

Notation "s [d sigmadsl ]" := (subst_dsl sigmadsl s) (at level 7, left associativity) : subst_scope.

Notation "[ sigmadsl ]" := (subst_dsl sigmadsl) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨d xidsl ⟩" := (ren_dsl xidsl s) (at level 7, left associativity) : subst_scope.

Notation "⟨ xidsl ⟩" := (ren_dsl xidsl) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_dsl,  Ren_dsl,  VarInstance_dsl.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_dsl,  Ren_dsl,  VarInstance_dsl in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_dsl| progress rewrite ?compComp_dsl| progress rewrite ?compComp'_dsl| progress rewrite ?rinstId_dsl| progress rewrite ?compRen_dsl| progress rewrite ?compRen'_dsl| progress rewrite ?renComp_dsl| progress rewrite ?renComp'_dsl| progress rewrite ?renRen_dsl| progress rewrite ?renRen'_dsl| progress rewrite ?varL_dsl| progress rewrite ?varLRen_dsl| progress (unfold up_ren, upRen_dsl_dsl, up_dsl_dsl)| progress (cbn [subst_dsl ren_dsl])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_dsl in *| progress rewrite ?compComp_dsl in *| progress rewrite ?compComp'_dsl in *| progress rewrite ?rinstId_dsl in *| progress rewrite ?compRen_dsl in *| progress rewrite ?compRen'_dsl in *| progress rewrite ?renComp_dsl in *| progress rewrite ?renComp'_dsl in *| progress rewrite ?renRen_dsl in *| progress rewrite ?renRen'_dsl in *| progress rewrite ?varL_dsl in *| progress rewrite ?varLRen_dsl in *| progress (unfold up_ren, upRen_dsl_dsl, up_dsl_dsl in * )| progress (cbn [subst_dsl ren_dsl] in * )| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_dsl).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_dsl).
