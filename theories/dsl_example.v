Lemma dsl_example : forall a, dsl nil  (Star (Star (Event a))) (Star (Event a)).
Proof.
move=> a.  

apply: ctrans=>//. apply: cstar=>//. apply: wrapinv=>//.

apply/ctrans=>//. apply/drop=>//.
apply/ctrans=>//. apply/wrapinv=>//.
apply/ctrans=>//. 2: { apply/wrap=>//. }
apply/cplus=>//. apply/cid=>//.
apply/ctrans=>//. apply/assoc=>//.
(*apply/guard=>//. left. pcofix CIH. pfold*)  

(*Just like cseq_ctx which was used in c_ineq we do the same now before applying dsl_fix. 
  Before the dsl_fix rule also 
  We went from event (e _;_ c, e _;_ c') step to (c,c') 
  and then remember (c,c') using cofix.
  This step is simulated by dsl by applying dsl_fix now
 *)
apply/cseq=>//. apply/cid=>//. (*Don't use rule_guard yet*) (*apply/rule_guard=>//. left=>//. pfold.*)

apply:(dsl_fix _). 


(*pfold_reverse. pcofix CIH. pfold.*) (*pcofix before cfix*)
(*apply/rule_cfix=>//. simpl=>//. *)

apply: ctrans.  (*rewrite /full_unf //=. *)
apply/cseq=>//. apply/cid=>//. apply/dropinv=>//.

apply/ctrans=>//. apply/cseq=>//. apply/cid=>//. apply/cstar/wrap=>//. 

(*again we apply dsl_fix instead of pcofix*)
apply:(dsl_fix _). 
(*pfold_reverse=>//. pcofix CIH2=>//. pfold=>//.*) (*pcofix before cfix*)
(*apply/cfix=>//. simpl=>//. *)



apply/ctrans. (*rewrite /full_unf //=. *) apply/cseq=>//. apply/wrapinv=>//. apply/cid=>//.
apply/ctrans=>//. apply/distR=>//.
apply/ctrans=>//. apply/cplus=>//. apply/proj=>//. apply/cid=>//.
apply/ctrans=>//. 2: { apply/drop=>//. }
apply/ctrans=>//. 2: { apply/wrap=>//. }

apply/ctrans=>//. 2: { apply/cplus=>//. apply/cid=>//. apply/cseq=>//. apply/cid=>//. apply/dropinv=>//. }
apply/ctrans=>//. 2: { apply/cplus=>//. apply/cid=>//. apply/distRinv=>//. }




apply/ctrans=>//. 2: { apply/cplus=>//. apply/cid=>//. apply/cplus=>//. apply/projinv=>//. apply/cid=>//. }
apply/ctrans=>//. 2: { apply/retag=>//. }
apply/ctrans=>//. 2: { apply/tagL=>//. }


apply/cplus=>//. 

apply/ctrans=>//. apply/cstar/wrapinv=>//. 
apply/ctrans=>//. apply/drop=>//.
apply/ctrans=>//. apply/wrapinv=>//.
apply/ctrans=>//. 2: { apply/wrap=>//. }
apply/cplus=>//. apply/cid=>//.
apply/ctrans=>//. apply/assoc=>//.
apply:(dsl_var _)=>//. rewrite !inE. lia.
(*exact:(dsl_var 1). *)
(*apply/guard=>//. right. apply/CIH.*)

apply/ctrans=>//. apply/assoc=>//.

apply:(dsl_var  _)=>//. 
(*exact:(dsl_var 0). *)
(*apply/guard=>//. right.  apply/CIH2.*)
Qed.
