From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Require Import Setoid List Streams Arith Recdef.

Infix "::" := Cons.
Infix "==" := EqSt (at level 70, no associativity).

Definition st_dec (A:Type)(s:Stream A) :=
  match s with a::s' => a::s' end.

Arguments st_dec {A}.

Lemma st_dec_eq : forall A (s:Stream A), s = st_dec s.
intros A [a s]; trivial.
Qed.
Arguments st_dec_eq [A].

Fixpoint nth (A: Type) (n: nat) (l: Stream A) {struct n}: A :=
match l with 
| Cons a l' => match n with O =>  a | S p => nth p l' end
end.

Arguments nth {A}.

CoFixpoint stroff A (f:nat->A) : Stream A :=
  f 0 :: stroff  (fun x => f (S x)) .

Arguments stroff {A}.

Lemma nth_stroff : forall (A:Type) n (f:nat->A), nth n (stroff f) = f n.
induction n; intros f; simpl; auto.
Qed.

Lemma ntheq_eqst :
  forall A (s1 s2 : Stream A),
   (forall n, nth n s1 = nth n s2) -> s1 == s2.
cofix CIH.
intros A s1 s2 q; destruct s1 as [a s1]; destruct s2 as [b s2]; constructor.
 exact (q 0). simpl. apply CIH. intros. move: (q (S n)). simpl. done.
Qed.

Lemma stroff_nth :
  forall A (s:Stream A), stroff (fun n => nth n s) == s.
intros; apply ntheq_eqst; intros; rewrite nth_stroff; auto.
Qed.

Lemma rule2 :
  forall A (a:A)(s:Stream A) (x:nat), 
  nth x (a::s) = match x with 0 => a | S p => nth p s end.
intros A a s x; case x; auto.
Qed.

Lemma rule2' :
  forall A (a:A)(s:Stream A) (x:nat),
  nth x (a::s) = if eq_nat_dec x 0 then a else nth (predn x) s.
intros A a s x; case x; auto.
Qed.

Lemma rule3 :
  forall A (f : nat -> A), hd (stroff f) = f 0.
intros; simpl; auto.
Qed.

Lemma rule4 :
  forall A (f : nat -> A), tl (stroff f) = stroff (fun x => f (S x)).
intros; simpl; auto.
Qed.

Lemma rule5 :
  forall A B (f : nat -> A)(e : A -> Stream A -> B),
  match stroff f with a::s => e a s end = e (f 0) (stroff (fun n => f (S n))).
intros A B f e; reflexivity.
Qed.

Section Map.
Variables A B : Set.
Variable f : A -> B.
CoFixpoint map (s:Stream A) : Stream B := 
Cons (f (hd s)) (map (tl s)).

Arguments map.

(* The right-hand side of the map definition is given by the following
   function.  In other words, map is a fixed point of this definition. *)
Definition map_F (map : Stream A -> Stream B) (s:Stream A) :=
   (f (hd s)) :: map (tl s).

Lemma sandbox_map : forall map':Stream A -> nat -> B,
 (forall s' y, map' s' y = nth y (map_F (fun s => stroff (map' s)) s')) ->
 forall s x, 
 map' s x = map' s x.
(* We suppose that map' satisfies the property of being the recursive
 representation of the co-recursive fixed point of map_F (hypothesis Hfix. *)
intros map' Hfix s x.
(* use the fixed-point assumption just now. *)
pattern (map' s x) at 2; rewrite Hfix; unfold map_F.
(* we replace the creation of a pattern-matching construct by an if-then-else
  construct: thus avoiding bound variables. *)
rewrite rule2'.
rewrite nth_stroff.
(* At this point, the right hand side of the equation is the right hand side
 of recursive definition for map', but not the one in the paper. because
 there is an if_then_else instead of a "match ... with". *)
Abort.

(* This second experiment describes an approach that sticks more closely to
 the pattern-matching approach.  However, we do not manage to make the whole
 code of the function visible in one single goal. *)

Lemma sandbox_map' : forall map':Stream A -> nat -> B,
 (forall s' y, map' s' y = nth y (map_F (fun s => stroff (map' s)) s')) ->
 forall s x, 
 map' s x = map' s x.
(* Same proof header as above. *)
intros map' Hfix s x.
pattern (map' s x) at 2; rewrite Hfix; unfold map_F.
rewrite rule2.
(* We need to work inside the body of pattern-matching rules.  For this,
  we will perform in the proof the case analysis that happens in the code,
  this will yield two subgoals with simplified values.  We need to remember
  that the code to produce should of the form
   match x with 0 => V1 | S p => V2 end
   where V1 and V2 are the values that we can recover from our work on
   the first and second goal. *)
destruct x as [ | p ].
(* Here we gather that V1 = f (hd s). *)
rewrite Hfix; auto.
(* After getting rid of the first goal, we can observe the second one. *)
rewrite nth_stroff.
(* Here we gather that V2 = map' (tl s) p *)
Abort.

(* Now there is the question of taking arguments as functions or as streams.
  Defining a function that takes arguments as functions relies on the
  same map_F function. *)

(*Several variable end up being used in wrong contexts.  The variable s'
 that used to be used as a stream is now a function, the coercion must be
 added. The function passed as argument to map_F is supposed to take a
 stream as argument and return a stream, but map', which returns a function
 and takes a function as argument is passed instead. *)
Lemma sandbox_map' : forall map': (nat -> A) -> nat -> B,
 (forall s' y, map' s' y = 
  nth y (map_F (fun s => stroff (map' (fun x => nth x s))) (stroff s'))) ->
 forall s x, 
 map' s x = map' s x.
intros map' Hfix s x.
pattern (map' s x) at 2; rewrite Hfix; unfold map_F.
rewrite rule3.
rewrite rule2.
(* remember that the right hand-side has the form:
   match x with 0 => V1 | S p => V2 end. *)
destruct x as [ | p].
(* Now We now that V1 = f (s 0) *)
admit.
rewrite nth_stroff.
(* Now, provide a new sandbox to reason on the function passed as argument to 
  map'.
  Because of the context, we now that the value V2 should be
  map' ?V3 p, but we want to refine V3. *)
match goal with |- _ = map' ?f ?k =>  assert (forall x, f x = f x) end.
intros x.
(* Now V3 = fun x => V4 *)
 rewrite rule4.
rewrite nth_stroff.
(* So we know that V4 = s (S x) *)
(* This tells us that the complete right-hand side of definition is.
  match x with 0 => f (S 0) | S p => map' (fun x => s (S x)) p end *)
Abort.

(* We could make a fourth experiment with arguments streams-as-functions and
  using rule2' instead of rule2, but it is not very useful.  We still
  need to open an auxiliary sandbox to work inside the function. *)

Fixpoint map' (s : nat -> A) (x : nat) : B :=
  match x with 0 => f (s 0) | S p => map' (fun x => s (S x)) p end.

Lemma nth_map : 
forall n s, nth n (map s)= f (nth n s).
Proof.
induction n; simpl; intros [a s]; simpl; auto.
Qed.


(*Recursive map, or \fofstr(map)*)

Fixpoint rmap (s: nat -> A)(x: nat): B :=
match x with
| 0 => f (s 0)
| S p => rmap (fun (n: nat) => s (n+1)) p
end.


(*Form-shifting lemma:*)

Lemma rmapr: forall (s: nat -> A) (n: nat), 
rmap s n = f (s n). 
intros.
generalize s.
elim n.
simpl; auto.
intros.
simpl.
rewrite H.
rewrite plus_comm; auto.
Qed.

Lemma map_decomp: forall x s,
map (x :: s) =  (f x) :: (map s).
intros.
rewrite (st_dec_eq (map (Cons x s))); simpl.
auto.
Qed.

(*Equivalence of the two recursive representations of map.*)

Theorem map_rmap: forall n t,
nth n (map t) = rmap (fun (n: nat)=> nth n t) n.
Proof.
intros.
case t; elim n.
intros; simpl; auto.
intros; 
rewrite map_decomp;
rewrite rmapr; simpl; auto.
case s.
intros.
rewrite H.
simpl; rewrite rmapr; auto.
Qed.

End Map.

Section Zip.

Variable A B C : Set.
Variable f: A -> B -> C.

CoFixpoint zipWith (a:Stream A) (b:Stream B) : Stream C :=
f (hd a) (hd b)::zipWith (tl a) (tl b).

Definition zipWith_F (zpf : Stream A -> Stream B -> Stream C) 
 (a:Stream A) (b:Stream B) :=
  f (hd a) (hd b):: zpf (tl a) (tl b).

Lemma sandbox_zipWith: forall zpf : Stream A -> Stream B -> nat -> C,
 (forall a b y, zpf a b y =
                 nth y (zipWith_F (fun a b => stroff (zpf a b)) a b)) ->
 forall a b x, zpf a b x = zpf a b x.
intros zpf Hfix a b x.
pattern (zpf a b x) at 2; rewrite Hfix; unfold zipWith_F.
rewrite rule2'.
rewrite nth_stroff.
(* The left hand side is what we want. *)
Abort.

(* Second approach, with match-with *)
Lemma sandbox_zipWith: forall zpf : Stream A -> Stream B -> nat -> C,
 (forall a b y, zpf a b y =
                 nth y (zipWith_F (fun a b => stroff (zpf a b)) a b)) ->
 forall a b x, zpf a b x = zpf a b x.
intros zpf Hfix a b x.
pattern (zpf a b x) at 2; rewrite Hfix; unfold zipWith_F.
rewrite rule2.
(* value should be : V = match x with 0 => V1 | S p => V2 end *)
destruct x as [ | p].
(* V1 = f (hd a) (hd b) , as displayed in the goal *)
admit.
rewrite nth_stroff.
(* V2 = zpf (tl a) (tl b) p , as displayed in the goal. *)
Abort.

(* third approach, with function arguments. All instances of a and b
  are replaced by (stroff a) and (stroff b) to preserve typing, except
  when passed as argument to zpf *)

Lemma sandbox_zipWith : forall zpf : (nat -> A) -> (nat -> B) -> nat -> C,
  (forall a b y, zpf a b y =
                 nth y (zipWith_F 
                           (fun a b => stroff (zpf (fun x => nth x a) 
                                 (fun x => nth x b))) (stroff a) (stroff b))) ->
 forall a b x, zpf a b x = zpf a b x.
intros zpf Hfix a b x.
pattern (zpf a b x) at 2; rewrite Hfix; unfold zipWith_F.
rewrite rule2.
(* value should v = match x with 0 => V1 | S p => V2 end *)
destruct x as [| p].
repeat rewrite rule3.
(* V1 should be (f (a 0) (b 0)) *)
admit.
rewrite nth_stroff.
(* New sandbox the first function argument. *)
(* V2 = zpf (fun x => V3) (fun x => V4) p *)
match goal with |- _ = zpf ?f _ _ => assert (forall x, f x = f x) end.
intros x.
rewrite rule4.
rewrite nth_stroff.
(* We see : V3 = a (S x), etc... *)
admit.
match goal with |- _ = zpf _ ?f _ => assert (forall x, f x = f x) end.
intros x.
rewrite rule4.
rewrite nth_stroff.
(* We see : V4 = b (S x) *)
Abort.

Fixpoint zipWith' (a : nat -> A) (b : nat -> B) (x:nat) : C :=
  match x with 
    0 => f (a 0) (b 0)
  | S p => zipWith' (fun x => a (S x)) (fun x => b (S x)) p
  end.

Lemma Str_nth_tl_zipWith : forall n (a:Stream A) (b:Stream B),
 Str_nth_tl n (zipWith a b)= zipWith (Str_nth_tl n a) (Str_nth_tl n b).
Proof.
induction n.
reflexivity.
intros [x xs] [y ys].
unfold Str_nth in *.
simpl in *.
apply IHn.
Qed.

Lemma nth_zipWith : forall n (a:Stream A) (b:Stream B), nth n (zipWith a
 b)= f (nth n a) (nth n b).
Proof.
induction n; intros; destruct a as [x a]; destruct b as [y b]; simpl; auto.
Qed.

End Zip.


Lemma nth_S : forall A (s:Stream A) n,
  nth (S n) s = match s with _::s => nth n s end.
intros A [a s] n; auto.
Qed.

Lemma tl_nth_stroff : forall (A:Set) n (f:nat->A),
  nth n (tl (stroff f)) = f (S n).
simpl; intros A n f; rewrite nth_stroff; auto.
Qed.

Hint Rewrite nth_S nth_stroff tl_nth_stroff  nth_map nth_zipWith
  : str_mod.

Ltac str_eqn_tac :=
  intros; 
  match goal with
   | |- ?f == _ => unfold f
   | |- ?f _ == _ => unfold f
   | |- ?f _ _ == _ => unfold f
   | |- ?f _ _ _ == _ => unfold f
  end;
   apply ntheq_eqst; intros n; rewrite nth_stroff;
  match goal with
   | |- ?f' n = _ =>
      functional induction f' n; autorewrite with str_mod; auto
   | |- ?f' ?a n = _ => 
      functional induction f' a n; autorewrite with str_mod; auto
   | |- ?f' ?a ?b n = _ =>
      functional induction f' a b n; autorewrite with str_mod; auto
   | |- ?f' ?a ?b ?c n = _ =>
      functional induction f' a b c n; autorewrite with str_mod; auto
  end.

Function nats' (n:nat) : nat :=
  match n with 0 => 1 | S p => S (nats' p) end.

Definition nats := stroff nats'.

Lemma nats_eqn_decomposed_proof :
 nats == 1:: (map nat nat S nats).
unfold nats; apply ntheq_eqst; intro n; rewrite nth_stroff.
functional induction nats' n.
auto.
rewrite nth_S. rewrite nth_map. rewrite nth_stroff.
trivial.
Qed.

Lemma nats_eqn : nats == 1::map nat nat S nats.
str_eqn_tac.
Qed.

Definition fibs_F :=
  fun (fibs : Stream nat) => 1::1::zipWith nat nat nat plus fibs (tl fibs).

Lemma fibs_sandbox :
  forall (fibs : nat -> nat) n, 
   fibs n = nth n (fibs_F (stroff fibs)).
intros fibs n; unfold fibs_F.
rewrite rule2.
(* V = match n with 0 => V1 | S p => V2 end *)
destruct n as [ | p].
(* We learn that V1 is 1 *)
admit.
rewrite rule2.
(* V2 = match p with 0 => V3 | S q => V4 end *)
destruct p as [ | q].
(* We learn that V3 is 1 *)
admit.
rewrite nth_zipWith.
rewrite rule4.
repeat rewrite nth_stroff.
(* we learn that V4 is fibs q + fibs (S q); because of a limitation
  in the computation of structural recursion guards, we need to replace
   (S q) with p. *)
Abort.

Function fibs' (n:nat) : nat :=
  match n with
    0 => 1
  | S p => match p with
             0 => 1
           | S q => fibs' q + fibs' p
           end
  end.

Definition fibs := stroff fibs'.

Lemma fibs_eqn : fibs == 1::1::zipWith nat nat nat plus fibs (tl fibs).
str_eqn_tac.
Qed.

Definition dTimes_F :=
  fun (dtimes : Stream nat -> Stream nat -> Stream nat)
      (x y : Stream nat)  =>
     match x, y with
       x0::x', y0::y' => x0*y0::zipWith _ _ _ plus (dtimes x' y) (dtimes x y')
     end.

Lemma sandbox_dTimes :
  forall (dTimes : Stream nat -> Stream nat -> nat -> nat)
     x y n,
      dTimes x y n = nth n (dTimes_F (fun x y => stroff (dTimes x y)) x y).
intros dTimes x y n; unfold dTimes_F.
(* We know the value is match x with x0::x' => V1 end *)
destruct x as [x0 x'].
(* We know V1 is match y with y0::y' => V2 end *)
destruct y as [y0 y'].
rewrite rule2.
(* we know V2 is  match n with 0 => V3 | S p => V4 *)
destruct n as [ | p].
(* Now we know V3 is x0*y0 *)
admit.
rewrite nth_zipWith.
rewrite nth_stroff.
rewrite nth_stroff.
(* we know V4 is dTimes x' (y0::y') p + dTimes (x0 :: x') y' p; this
 can be abbreviated with:
   dTimes x' y p + dTimes x y' p *)
Abort.

Function dTimes' (x y:Stream nat) (n:nat) {struct n} : nat :=
  match x, y, n with
    x0 :: x', y0 :: y', 0 => x0 * y0
  | x0 :: x', y0 :: y', S p => dTimes' x' y p + dTimes' x y' p
  end.

Definition dTimes a b := stroff (dTimes' a b).

Lemma dTimes_eqn : 
  forall a b,  dTimes a b ==
     hd a * hd b :: zipWith nat nat nat plus (dTimes (tl a) b) (dTimes a (tl b)).
str_eqn_tac.
Qed.

Section Zeroes.

(* This example is given in the Types article, do not remove. *)

CoFixpoint Zeroes := Cons 0 Zeroes.

Fixpoint nzeroes (n: nat) :=
  match n with 0 => 0 | S p => nzeroes p end.

Lemma nth_zeroes: forall n, nth n Zeroes = nzeroes n. 
Proof.
 induction n; simpl; auto.
Qed.

Theorem zeroes_bisim: Zeroes == stroff (nzeroes).
Proof.
apply ntheq_eqst; intro; rewrite nth_stroff; apply nth_zeroes.
Qed.

End Zeroes.

Section Stream_Transformation.

Lemma Str_tr:
forall (A: Set) (a: A)
(s: Stream A) (n: nat),
(Str_nth n (a :: s)) =
 ( match n with
                    | 0 => a
                    | S p => Str_nth p s
                    end).
induction n; simpl; auto.
Qed.

End Stream_Transformation.
