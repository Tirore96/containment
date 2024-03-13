
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val implb : bool -> bool -> bool **)

let implb b1 b2 =
  if b1 then b2 else true

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y



type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a0, _) -> a0

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val tail_add : int -> int -> int **)

let rec tail_add n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n1 -> tail_add n1 (Stdlib.Int.succ m))
    n0

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun n1 -> tail_addmul (tail_add m r) n1 m)
    n0

(** val tail_mul : int -> int -> int **)

let tail_mul n0 m =
  tail_addmul 0 n0 m

(** val of_uint_acc : uint -> int -> int **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))))

(** val of_uint : uint -> int **)

let of_uint d =
  of_uint_acc d 0

(** val of_hex_uint_acc : uint0 -> int -> int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))
        acc))))))))))))))))

(** val of_hex_uint : uint0 -> int **)

let of_hex_uint d =
  of_hex_uint_acc d 0

(** val of_num_uint : uint1 -> int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

type reflect =
| ReflectT
| ReflectF

(** val sumbool_of_bool : bool -> bool **)

let sumbool_of_bool = function
| true -> true
| false -> false

(** val locked_with : unit -> 'a1 -> 'a1 **)

let locked_with _ x =
  x

module Option =
 struct
  (** val apply : ('a1 -> 'a2) -> 'a2 -> 'a1 option -> 'a2 **)

  let apply f x = function
  | Some y -> f y
  | None -> x

  (** val bind :
      ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

  let bind f =
    apply f None
 end

type ('aT, 'rT) simpl_fun =
  'aT -> 'rT
  (* singleton inductive, whose constructor was SimplFun *)

(** val fun_of_simpl : ('a1, 'a2) simpl_fun -> 'a1 -> 'a2 **)

let fun_of_simpl f =
  f

(** val comp : ('a2 -> 'a1) -> ('a3 -> 'a2) -> 'a3 -> 'a1 **)

let comp f g x =
  f (g x)

(** val pcomp :
    ('a2 -> 'a1 option) -> ('a3 -> 'a2 option) -> 'a3 -> 'a1
    option **)

let pcomp f g x =
  Option.bind f (g x)

(** val tag : ('a1, 'a2) sigT -> 'a1 **)

let tag =
  projT1

(** val tagged : ('a1, 'a2) sigT -> 'a2 **)

let tagged =
  projT2

(** val tagged0 : 'a1 -> 'a2 -> ('a1, 'a2) sigT **)

let tagged0 i x =
  ExistT (i, x)

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

type alt_spec =
| AltTrue
| AltFalse

(** val altP : bool -> reflect -> alt_spec **)

let altP _ pb =
  let _evar_0_ = fun _ _ -> AltTrue in
  let _evar_0_0 = fun _ _ -> AltFalse in
  (match pb with
   | ReflectT -> _evar_0_ __ __
   | ReflectF -> _evar_0_0 __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred = 't -> bool

type 't predType =
  __ -> 't pred
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

type 't simpl_pred = ('t, bool) simpl_fun

(** val simplPred : 'a1 pred -> 'a1 simpl_pred **)

let simplPred p =
  p

module PredOfSimpl =
 struct
  (** val coerce : 'a1 simpl_pred -> 'a1 pred **)

  let coerce =
    fun_of_simpl
 end

type 't rel = 't -> 't pred

type 't mem_pred =
  't pred
  (* singleton inductive, whose constructor was Mem *)

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  Obj.magic mp

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

(** val mem :
    'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT

type 't eq_axiom = 't -> 't -> reflect

module Coq_hasDecEq =
 struct
  type 't axioms_ = { eq_op : 't rel; eqP : 't eq_axiom }

  (** val eq_op : 'a1 axioms_ -> 'a1 rel **)

  let eq_op record =
    record.eq_op

  (** val eqP : 'a1 axioms_ -> 'a1 eq_axiom **)

  let eqP record =
    record.eqP
 end

module Equality =
 struct
  type 't axioms_ =
    't Coq_hasDecEq.axioms_
    (* singleton inductive, whose constructor was Class *)

  (** val eqtype_hasDecEq_mixin :
      'a1 axioms_ -> 'a1 Coq_hasDecEq.axioms_ **)

  let eqtype_hasDecEq_mixin record =
    record

  type coq_type =
    __ axioms_
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort axioms_ **)

  let coq_class record =
    record
 end

(** val eq_op0 : Equality.coq_type -> Equality.sort rel **)

let eq_op0 s =
  (Equality.eqtype_hasDecEq_mixin (Equality.coq_class s)).Coq_hasDecEq.eq_op

(** val eqP0 : Equality.coq_type -> Equality.sort eq_axiom **)

let eqP0 s =
  (Equality.eqtype_hasDecEq_mixin (Equality.coq_class s)).Coq_hasDecEq.eqP

type eq_xor_neq =
| EqNotNeq
| NeqNotEq

(** val eqVneq :
    Equality.coq_type -> Equality.sort -> Equality.sort ->
    eq_xor_neq **)

let eqVneq t x y =
  let _evar_0_ = fun _ -> EqNotNeq in
  let _evar_0_0 = fun _ -> NeqNotEq in
  (match altP (eq_op0 t x y) (eqP0 t x y) with
   | AltTrue -> _evar_0_ __
   | AltFalse -> _evar_0_0 __)

module Coq_isSub =
 struct
  type ('t, 'sub_sort) axioms_ = { val_subdef : ('sub_sort ->
                                                't);
                                   coq_Sub : ('t -> __ ->
                                             'sub_sort);
                                   coq_Sub_rect : (__ -> ('t
                                                  -> __ ->
                                                  __) ->
                                                  'sub_sort
                                                  -> __) }

  (** val val_subdef :
      'a1 pred -> ('a1, 'a2) axioms_ -> 'a2 -> 'a1 **)

  let val_subdef _ record =
    record.val_subdef

  (** val coq_Sub :
      'a1 pred -> ('a1, 'a2) axioms_ -> 'a1 -> 'a2 **)

  let coq_Sub _ record x =
    record.coq_Sub x __
 end

module SubType =
 struct
  type ('t, 's) axioms_ =
    ('t, 's) Coq_isSub.axioms_
    (* singleton inductive, whose constructor was Class *)

  (** val eqtype_isSub_mixin :
      'a1 pred -> ('a1, 'a2) axioms_ -> ('a1, 'a2)
      Coq_isSub.axioms_ **)

  let eqtype_isSub_mixin _ record =
    record

  type 't coq_type =
    ('t, __) axioms_
    (* singleton inductive, whose constructor was Pack *)

  type 't sort = __

  (** val coq_class :
      'a1 pred -> 'a1 coq_type -> ('a1, 'a1 sort) axioms_ **)

  let coq_class _ record =
    record

  (** val phant_on_ :
      'a1 pred -> 'a1 coq_type -> ('a1, 'a1 sort) axioms_ **)

  let phant_on_ =
    coq_class
 end

(** val sub0 :
    'a1 pred -> 'a1 SubType.coq_type -> 'a1 -> 'a1
    SubType.sort **)

let sub0 p s x =
  Coq_isSub.coq_Sub p
    (SubType.eqtype_isSub_mixin p (SubType.coq_class p s)) x

(** val insub :
    'a1 pred -> 'a1 SubType.coq_type -> 'a1 -> 'a1
    SubType.sort option **)

let insub p sT x =
  match idP (p x) with
  | ReflectT -> Some (sub0 p sT x)
  | ReflectF -> None

type ('t, 'x) inj_type = 't

type ('t, 'x) pcan_type = 't

(** val inj_eqAxiom :
    Equality.coq_type -> ('a1 -> Equality.sort) -> 'a1
    eq_axiom **)

let inj_eqAxiom eT f x y =
  iffP (eq_op0 eT (f x) (f y)) (eqP0 eT (f x) (f y))

(** val pair_eq :
    Equality.coq_type -> Equality.coq_type ->
    (Equality.sort * Equality.sort) rel **)

let pair_eq t1 t2 u v =
  (&&) (eq_op0 t1 (fst u) (fst v)) (eq_op0 t2 (snd u) (snd v))

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type ->
    (Equality.sort * Equality.sort) eq_axiom **)

let pair_eqP t1 t2 __top_assumption_ =
  let _evar_0_ = fun x1 x2 __top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP
        ((&&) (eq_op0 t1 (fst (x1, x2)) (fst (y1, y2)))
          (eq_op0 t2 (snd (x1, x2)) (snd (y1, y2))))
        (andP (eq_op0 t1 (fst (x1, x2)) (fst (y1, y2)))
          (eq_op0 t2 (snd (x1, x2)) (snd (y1, y2))))
    in
    let (a0, b0) = __top_assumption_0 in _evar_0_ a0 b0
  in
  let (a0, b0) = __top_assumption_ in _evar_0_ a0 b0

(** val hB_unnamed_factory_41 :
    Equality.coq_type -> Equality.coq_type ->
    (Equality.sort * Equality.sort) Coq_hasDecEq.axioms_ **)

let hB_unnamed_factory_41 t1 t2 =
  { Coq_hasDecEq.eq_op = (pair_eq t1 t2); Coq_hasDecEq.eqP =
    (pair_eqP t1 t2) }

(** val datatypes_prod__canonical__eqtype_Equality :
    Equality.coq_type -> Equality.coq_type ->
    Equality.coq_type **)

let datatypes_prod__canonical__eqtype_Equality t1 t2 =
  Obj.magic hB_unnamed_factory_41 t1 t2

(** val eqn : int -> int -> bool **)

let rec eqn m n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      n0)
    (fun m' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n' -> eqn m' n')
      n0)
    m

(** val eqnP : int eq_axiom **)

let eqnP n0 m =
  iffP (eqn n0 m) (idP (eqn n0 m))

(** val hB_unnamed_factory_1 : int Coq_hasDecEq.axioms_ **)

let hB_unnamed_factory_1 =
  { Coq_hasDecEq.eq_op = eqn; Coq_hasDecEq.eqP = eqnP }

(** val datatypes_nat__canonical__eqtype_Equality :
    Equality.coq_type **)

let datatypes_nat__canonical__eqtype_Equality =
  Obj.magic hB_unnamed_factory_1

(** val addn_rec : int -> int -> int **)

let addn_rec =
  add

(** val addn : int -> int -> int **)

let addn =
  addn_rec

(** val subn_rec : int -> int -> int **)

let subn_rec =
  sub

(** val subn : int -> int -> int **)

let subn =
  subn_rec

(** val leq : int -> int -> bool **)

let leq m n0 =
  eq_op0 datatypes_nat__canonical__eqtype_Equality
    (Obj.magic subn m n0) (Obj.magic 0)

(** val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter n0 f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i -> f (iter i f x))
    n0

(** val size : 'a1 list -> int **)

let rec size = function
| [] -> 0
| _ :: s' -> Stdlib.Int.succ (size s')

(** val ncons : int -> 'a1 -> 'a1 list -> 'a1 list **)

let ncons n0 x =
  iter n0 (fun x0 -> x :: x0)

(** val nseq : int -> 'a1 -> 'a1 list **)

let nseq n0 x =
  ncons n0 x []

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val nth : 'a1 -> 'a1 list -> int -> 'a1 **)

let rec nth x0 s n0 =
  match s with
  | [] -> x0
  | x :: s' ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> x)
       (fun n' -> nth x0 s' n')
       n0)

(** val has : 'a1 pred -> 'a1 list -> bool **)

let rec has a0 = function
| [] -> false
| x :: s' -> (||) (a0 x) (has a0 s')

(** val all : 'a1 pred -> 'a1 list -> bool **)

let rec all a0 = function
| [] -> true
| x :: s' -> (&&) (a0 x) (all a0 s')

(** val eqseq :
    Equality.coq_type -> Equality.sort list -> Equality.sort
    list -> bool **)

let rec eqseq t s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _ :: _ -> false)
  | x1 :: s1' ->
    (match s2 with
     | [] -> false
     | x2 :: s2' -> (&&) (eq_op0 t x1 x2) (eqseq t s1' s2'))

(** val eqseqP :
    Equality.coq_type -> Equality.sort list eq_axiom **)

let eqseqP t _top_assumption_ =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match __top_assumption_ with
     | [] -> _evar_0_
     | a0 :: l -> _evar_0_0 a0 l)
  in
  let _evar_0_0 = fun x1 s1 iHs __top_assumption_ ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 s2 ->
      let __top_assumption_0 = eqP0 t x1 x2 in
      let _evar_0_1 = fun _ -> iffP (eqseq t s1 s2) (iHs s2)
      in
      let _evar_0_2 = fun _ -> ReflectF in
      (match __top_assumption_0 with
       | ReflectT -> _evar_0_1 __
       | ReflectF -> _evar_0_2 __)
    in
    (match __top_assumption_ with
     | [] -> _evar_0_0
     | a0 :: l -> _evar_0_1 a0 l)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _top_assumption_

(** val hB_unnamed_factory_0 :
    Equality.coq_type -> Equality.sort list
    Coq_hasDecEq.axioms_ **)

let hB_unnamed_factory_0 t =
  { Coq_hasDecEq.eq_op = (eqseq t); Coq_hasDecEq.eqP =
    (eqseqP t) }

(** val datatypes_list__canonical__eqtype_Equality :
    Equality.coq_type -> Equality.coq_type **)

let datatypes_list__canonical__eqtype_Equality t =
  Obj.magic hB_unnamed_factory_0 t

(** val mem_seq :
    Equality.coq_type -> Equality.sort list -> Equality.sort
    -> bool **)

let rec mem_seq t = function
| [] -> (fun _ -> false)
| y :: s' ->
  let p = mem_seq t s' in (fun x -> (||) (eq_op0 t x y) (p x))

type seq_eqclass = Equality.sort list

(** val pred_of_seq :
    Equality.coq_type -> seq_eqclass -> Equality.sort
    pred_sort **)

let pred_of_seq t s =
  Obj.magic mem_seq t s

(** val seq_predType :
    Equality.coq_type -> Equality.sort predType **)

let seq_predType t =
  Obj.magic pred_of_seq t

(** val undup :
    Equality.coq_type -> Equality.sort list -> Equality.sort
    list **)

let rec undup t = function
| [] -> []
| x :: s' ->
  if in_mem x (mem (seq_predType t) (Obj.magic s'))
  then undup t s'
  else x :: (undup t s')

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| x :: s' -> (f x) :: (map f s')

(** val pmap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list **)

let rec pmap f = function
| [] -> []
| x :: s' ->
  let r = pmap f s' in
  Option.apply (fun x0 -> x0 :: r) r (f x)

(** val iota : int -> int -> int list **)

let rec iota m n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> m :: (iota (Stdlib.Int.succ m) n'))
    n0

(** val foldr :
    ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten s =
  foldr cat [] s

module Coq_hasChoice =
 struct
  type 't axioms_ =
    't pred -> int -> 't option
    (* singleton inductive, whose constructor was Axioms_ *)

  (** val find_subdef :
      'a1 axioms_ -> 'a1 pred -> int -> 'a1 option **)

  let find_subdef record =
    record

  type 't phant_axioms = 't axioms_
 end

module Choice =
 struct
  type 't axioms_ = { choice_hasChoice_mixin : 't
                                               Coq_hasChoice.axioms_;
                      eqtype_hasDecEq_mixin : 't
                                              Coq_hasDecEq.axioms_ }

  (** val choice_hasChoice_mixin :
      'a1 axioms_ -> 'a1 Coq_hasChoice.axioms_ **)

  let choice_hasChoice_mixin record =
    record.choice_hasChoice_mixin

  (** val eqtype_hasDecEq_mixin :
      'a1 axioms_ -> 'a1 Coq_hasDecEq.axioms_ **)

  let eqtype_hasDecEq_mixin record =
    record.eqtype_hasDecEq_mixin

  type coq_type =
    __ axioms_
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort axioms_ **)

  let coq_class record =
    record

  module Exports =
   struct
    (** val choice_Choice_class__to__eqtype_Equality_class :
        'a1 axioms_ -> 'a1 Equality.axioms_ **)

    let choice_Choice_class__to__eqtype_Equality_class c =
      c.eqtype_hasDecEq_mixin

    (** val choice_Choice__to__eqtype_Equality :
        coq_type -> Equality.coq_type **)

    let choice_Choice__to__eqtype_Equality s =
      choice_Choice_class__to__eqtype_Equality_class
        (coq_class s)
   end
 end

(** val find_subdef0 :
    Choice.coq_type -> Choice.sort pred -> int -> Choice.sort
    option **)

let find_subdef0 s x x0 =
  Coq_hasChoice.find_subdef
    (Choice.coq_class s).Choice.choice_hasChoice_mixin x x0

(** val pCanHasChoice :
    Choice.coq_type -> ('a1 -> Choice.sort) -> (Choice.sort
    -> 'a1 option) -> 'a1 Coq_hasChoice.phant_axioms **)

let pCanHasChoice t _ f' =
  let liftP = fun sP ->
    simplPred (fun x -> Option.apply sP false (f' x))
  in
  let sf = fun sP n0 ->
    Option.bind f'
      (find_subdef0 t (PredOfSimpl.coerce (liftP sP)) n0)
  in
  (fun sP -> fun_of_simpl (sf sP))

(** val nat_hasChoice : int Coq_hasChoice.phant_axioms **)

let nat_hasChoice =
  let f = fun p n0 -> if p n0 then Some n0 else None in
  (fun p -> fun_of_simpl (f p))

(** val hB_unnamed_factory_21 :
    int Coq_hasChoice.phant_axioms **)

let hB_unnamed_factory_21 =
  nat_hasChoice

module Choice_isCountable =
 struct
  type 't axioms_ = { pickle : ('t -> int);
                      unpickle : (int -> 't option) }

  (** val pickle : 'a1 axioms_ -> 'a1 -> int **)

  let pickle record =
    record.pickle

  (** val unpickle : 'a1 axioms_ -> int -> 'a1 option **)

  let unpickle record =
    record.unpickle
 end

module Countable =
 struct
  type 't axioms_ = { choice_hasChoice_mixin : 't
                                               Coq_hasChoice.axioms_;
                      eqtype_hasDecEq_mixin : 't
                                              Coq_hasDecEq.axioms_;
                      choice_Choice_isCountable_mixin : 
                      't Choice_isCountable.axioms_ }

  (** val choice_hasChoice_mixin :
      'a1 axioms_ -> 'a1 Coq_hasChoice.axioms_ **)

  let choice_hasChoice_mixin record =
    record.choice_hasChoice_mixin

  (** val eqtype_hasDecEq_mixin :
      'a1 axioms_ -> 'a1 Coq_hasDecEq.axioms_ **)

  let eqtype_hasDecEq_mixin record =
    record.eqtype_hasDecEq_mixin

  (** val choice_Choice_isCountable_mixin :
      'a1 axioms_ -> 'a1 Choice_isCountable.axioms_ **)

  let choice_Choice_isCountable_mixin record =
    record.choice_Choice_isCountable_mixin

  type coq_type =
    __ axioms_
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort axioms_ **)

  let coq_class record =
    record

  module Exports =
   struct
    (** val choice_Countable_class__to__choice_Choice_class :
        'a1 axioms_ -> 'a1 Choice.axioms_ **)

    let choice_Countable_class__to__choice_Choice_class c =
      { Choice.choice_hasChoice_mixin =
        c.choice_hasChoice_mixin;
        Choice.eqtype_hasDecEq_mixin =
        c.eqtype_hasDecEq_mixin }

    (** val choice_Countable__to__choice_Choice :
        coq_type -> Choice.coq_type **)

    let choice_Countable__to__choice_Choice s =
      choice_Countable_class__to__choice_Choice_class
        (coq_class s)
   end
 end

(** val pickle0 :
    Countable.coq_type -> Countable.sort -> int **)

let pickle0 s x =
  (Countable.coq_class s).Countable.choice_Choice_isCountable_mixin.Choice_isCountable.pickle
    x

(** val unpickle0 :
    Countable.coq_type -> int -> Countable.sort option **)

let unpickle0 s x =
  (Countable.coq_class s).Countable.choice_Choice_isCountable_mixin.Choice_isCountable.unpickle
    x

module Coq_isCountable =
 struct
  type 't axioms_ = { pickle : ('t -> int);
                      unpickle : (int -> 't option) }

  (** val pickle : 'a1 axioms_ -> 'a1 -> int **)

  let pickle record =
    record.pickle

  (** val unpickle : 'a1 axioms_ -> int -> 'a1 option **)

  let unpickle record =
    record.unpickle

  (** val phant_Build :
      ('a1 -> int) -> (int -> 'a1 option) -> 'a1 axioms_ **)

  let phant_Build pickle1 unpickle1 =
    { pickle = pickle1; unpickle = unpickle1 }

  type 't phant_axioms = 't axioms_
 end

(** val pCanIsCountable :
    Countable.coq_type -> ('a1 -> Countable.sort) ->
    (Countable.sort -> 'a1 option) -> 'a1
    Coq_isCountable.axioms_ **)

let pCanIsCountable t f f' =
  Coq_isCountable.phant_Build (comp (pickle0 t) f)
    (pcomp f' (unpickle0 t))

(** val hB_unnamed_factory_89 :
    Countable.coq_type -> ('a1 -> Countable.sort) ->
    (Countable.sort -> 'a1 option) -> ('a1, Countable.sort)
    pcan_type Coq_isCountable.phant_axioms **)

let hB_unnamed_factory_89 =
  pCanIsCountable

(** val hB_unnamed_mixin_108 :
    Countable.coq_type -> Countable.sort pred ->
    Countable.sort SubType.coq_type -> Choice.sort
    SubType.sort Coq_hasChoice.phant_axioms **)

let hB_unnamed_mixin_108 t p sT =
  pCanHasChoice
    (Countable.Exports.choice_Countable__to__choice_Choice t)
    (SubType.eqtype_isSub_mixin p (SubType.phant_on_ p sT)).Coq_isSub.val_subdef
    (insub p sT)

(** val hB_unnamed_mixin_109 :
    Countable.coq_type -> Countable.sort pred ->
    Countable.sort SubType.coq_type -> (Equality.sort
    SubType.sort, Equality.sort) inj_type Coq_hasDecEq.axioms_ **)

let hB_unnamed_mixin_109 t p sT =
  { Coq_hasDecEq.eq_op = (fun x y ->
    eq_op0
      (Choice.Exports.choice_Choice__to__eqtype_Equality
        (Countable.Exports.choice_Countable__to__choice_Choice
          t))
      ((SubType.eqtype_isSub_mixin p (SubType.phant_on_ p sT)).Coq_isSub.val_subdef
        x)
      ((SubType.eqtype_isSub_mixin p (SubType.phant_on_ p sT)).Coq_isSub.val_subdef
        y)); Coq_hasDecEq.eqP =
    (inj_eqAxiom
      (Choice.Exports.choice_Choice__to__eqtype_Equality
        (Countable.Exports.choice_Countable__to__choice_Choice
          t))
      (SubType.eqtype_isSub_mixin p (SubType.phant_on_ p sT)).Coq_isSub.val_subdef) }

(** val hB_unnamed_mixin_111 :
    Countable.coq_type -> Countable.sort pred ->
    Countable.sort SubType.coq_type -> (Countable.sort
    SubType.sort, Countable.sort) pcan_type
    Choice_isCountable.axioms_ **)

let hB_unnamed_mixin_111 t p sT =
  { Choice_isCountable.pickle =
    (hB_unnamed_factory_89 t
      (SubType.eqtype_isSub_mixin p (SubType.phant_on_ p sT)).Coq_isSub.val_subdef
      (insub p sT)).Coq_isCountable.pickle;
    Choice_isCountable.unpickle =
    (hB_unnamed_factory_89 t
      (SubType.eqtype_isSub_mixin p (SubType.phant_on_ p sT)).Coq_isSub.val_subdef
      (insub p sT)).Coq_isCountable.unpickle }

(** val eqtype_sub_type_of__canonical__choice_Countable :
    Countable.coq_type -> Countable.sort pred ->
    Countable.sort SubType.coq_type -> Countable.coq_type **)

let eqtype_sub_type_of__canonical__choice_Countable t p sT =
  { Countable.choice_hasChoice_mixin =
    (hB_unnamed_mixin_108 t p sT);
    Countable.eqtype_hasDecEq_mixin =
    (hB_unnamed_mixin_109 t p sT);
    Countable.choice_Choice_isCountable_mixin =
    (hB_unnamed_mixin_111 t p sT) }

(** val hB_unnamed_factory_123 :
    int Choice_isCountable.axioms_ **)

let hB_unnamed_factory_123 =
  { Choice_isCountable.pickle = (fun x -> x);
    Choice_isCountable.unpickle = (fun x -> Some x) }

(** val datatypes_nat__canonical__choice_Countable :
    Countable.coq_type **)

let datatypes_nat__canonical__choice_Countable =
  { Countable.choice_hasChoice_mixin =
    (Obj.magic hB_unnamed_factory_21);
    Countable.eqtype_hasDecEq_mixin =
    (Obj.magic hB_unnamed_factory_1);
    Countable.choice_Choice_isCountable_mixin =
    (Obj.magic hB_unnamed_factory_123) }

module Coq_isFinite =
 struct
  type 't axioms_ =
    't list
    (* singleton inductive, whose constructor was Axioms_ *)

  (** val enum_subdef :
      'a1 Coq_hasDecEq.axioms_ -> 'a1 axioms_ -> 'a1 list **)

  let enum_subdef _ record =
    record
 end

module Finite =
 struct
  type 't axioms_ = { choice_hasChoice_mixin : 't
                                               Coq_hasChoice.axioms_;
                      choice_Choice_isCountable_mixin : 
                      't Choice_isCountable.axioms_;
                      eqtype_hasDecEq_mixin : 't
                                              Coq_hasDecEq.axioms_;
                      fintype_isFinite_mixin : 't
                                               Coq_isFinite.axioms_ }

  (** val eqtype_hasDecEq_mixin :
      'a1 axioms_ -> 'a1 Coq_hasDecEq.axioms_ **)

  let eqtype_hasDecEq_mixin record =
    record.eqtype_hasDecEq_mixin

  (** val fintype_isFinite_mixin :
      'a1 axioms_ -> 'a1 Coq_isFinite.axioms_ **)

  let fintype_isFinite_mixin record =
    record.fintype_isFinite_mixin

  type coq_type =
    __ axioms_
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort axioms_ **)

  let coq_class record =
    record

  module Exports =
   struct
    (** val fintype_Finite_class__to__eqtype_Equality_class :
        'a1 axioms_ -> 'a1 Equality.axioms_ **)

    let fintype_Finite_class__to__eqtype_Equality_class c =
      c.eqtype_hasDecEq_mixin

    (** val fintype_Finite__to__eqtype_Equality :
        coq_type -> Equality.coq_type **)

    let fintype_Finite__to__eqtype_Equality s =
      fintype_Finite_class__to__eqtype_Equality_class
        (coq_class s)
   end
 end

module FiniteNES =
 struct
  module Finite =
   struct
    module type Coq_enumLocked =
     sig
      val body : Finite.coq_type -> Finite.sort list
     end

    module Coq_enum =
     struct
      (** val body : Finite.coq_type -> Finite.sort list **)

      let body t =
        Coq_isFinite.enum_subdef
          (Finite.coq_class t).Finite.eqtype_hasDecEq_mixin
          (Finite.coq_class t).Finite.fintype_isFinite_mixin

      (** val unlock : __ **)

      let unlock =
        __
     end
   end
 end

type ordinal =
  int
  (* singleton inductive, whose constructor was Ordinal *)

(** val nat_of_ord : int -> ordinal -> int **)

let nat_of_ord _ i =
  i

(** val hB_unnamed_factory_58 :
    int -> (int, ordinal) Coq_isSub.axioms_ **)

let hB_unnamed_factory_58 n0 =
  { Coq_isSub.val_subdef = (nat_of_ord n0);
    Coq_isSub.coq_Sub = (fun x _ -> x);
    Coq_isSub.coq_Sub_rect = (fun _ k_S u -> k_S u __) }

(** val fintype_ordinal__canonical__eqtype_SubType :
    int -> int SubType.coq_type **)

let fintype_ordinal__canonical__eqtype_SubType n0 =
  Obj.magic hB_unnamed_factory_58 n0

(** val hB_unnamed_factory_60 :
    int -> ordinal Countable.axioms_ **)

let hB_unnamed_factory_60 n0 =
  Obj.magic Countable.coq_class
    (eqtype_sub_type_of__canonical__choice_Countable
      datatypes_nat__canonical__choice_Countable (fun x ->
      leq (Stdlib.Int.succ (Obj.magic x)) n0)
      (Obj.magic fintype_ordinal__canonical__eqtype_SubType
        n0))

(** val hB_unnamed_mixin_64 :
    int -> ordinal Coq_hasDecEq.axioms_ **)

let hB_unnamed_mixin_64 n0 =
  (hB_unnamed_factory_60 n0).Countable.eqtype_hasDecEq_mixin

(** val fintype_ordinal__canonical__eqtype_Equality :
    int -> Equality.coq_type **)

let fintype_ordinal__canonical__eqtype_Equality n0 =
  Obj.magic hB_unnamed_mixin_64 n0

(** val hB_unnamed_mixin_65 :
    int -> ordinal Coq_hasChoice.axioms_ **)

let hB_unnamed_mixin_65 n0 =
  (hB_unnamed_factory_60 n0).Countable.choice_hasChoice_mixin

(** val hB_unnamed_mixin_66 :
    int -> ordinal Choice_isCountable.axioms_ **)

let hB_unnamed_mixin_66 n0 =
  (hB_unnamed_factory_60 n0).Countable.choice_Choice_isCountable_mixin

(** val ord_enum : int -> ordinal list **)

let ord_enum n0 =
  pmap
    (Obj.magic insub (fun x -> leq (Stdlib.Int.succ x) n0)
      (fintype_ordinal__canonical__eqtype_SubType n0))
    (iota 0 n0)

(** val hB_unnamed_factory_67 :
    int -> ordinal Coq_isFinite.axioms_ **)

let hB_unnamed_factory_67 =
  ord_enum

(** val fintype_ordinal__canonical__fintype_Finite :
    int -> Finite.coq_type **)

let fintype_ordinal__canonical__fintype_Finite n0 =
  { Finite.choice_hasChoice_mixin =
    (Obj.magic hB_unnamed_mixin_65 n0);
    Finite.choice_Choice_isCountable_mixin =
    (Obj.magic hB_unnamed_mixin_66 n0);
    Finite.eqtype_hasDecEq_mixin =
    (Obj.magic hB_unnamed_mixin_64 n0);
    Finite.fintype_isFinite_mixin =
    (Obj.magic hB_unnamed_factory_67 n0) }

(** val ord0 : int -> ordinal **)

let ord0 _ =
  0

type ('r, 'i) bigbody =
| BigBody of 'i * ('r -> 'r -> 'r) * bool * 'r

(** val applybig : ('a1, 'a2) bigbody -> 'a1 -> 'a1 **)

let applybig body0 x =
  let BigBody (_, op, b0, v) = body0 in
  if b0 then op v x else x

(** val reducebig :
    'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1 **)

let reducebig idx0 r body0 =
  foldr (comp applybig body0) idx0 r

module type Coq_bigopLocked =
 sig
  val body :
    'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1
 end

module Coq_bigop =
 struct
  (** val body :
      'a1 -> 'a2 list -> ('a2 -> ('a1, 'a2) bigbody) -> 'a1 **)

  let body =
    reducebig

  (** val unlock : __ **)

  let unlock =
    __
 end

(** val index_enum_key : unit **)

let index_enum_key =
  ()

(** val index_enum : Finite.coq_type -> Finite.sort list **)

let index_enum t =
  locked_with index_enum_key
    (FiniteNES.Finite.Coq_enum.body t)

(** val cast : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let cast _ _ x =
  x

type ('t, 's) cell = { hd : 't; tl : 's }

module PolyType =
 struct
  type 't coq_sig =
    't
    (* singleton inductive, whose constructor was exist *)

  (** val sval : 'a1 coq_sig -> 'a1 **)

  let sval s =
    s

  type 't seq =
  | Coq_nil
  | Coq_cons of 't * 't seq

  (** val seq_rect :
      'a2 -> ('a1 -> 'a1 seq -> 'a2 -> 'a2) -> 'a1 seq -> 'a2 **)

  let rec seq_rect f f0 = function
  | Coq_nil -> f
  | Coq_cons (y, s0) -> f0 y s0 (seq_rect f f0 s0)

  (** val size : 'a1 seq -> int **)

  let rec size = function
  | Coq_nil -> 0
  | Coq_cons (_, xs0) -> Stdlib.Int.succ (size xs0)
 end

type fin = __

(** val nth_fin : 'a1 PolyType.seq -> fin -> 'a1 **)

let rec nth_fin xs n0 =
  match xs with
  | PolyType.Coq_nil -> assert false (* absurd case *)
  | PolyType.Coq_cons (x, xs0) ->
    (match Obj.magic n0 with
     | Some n1 -> nth_fin xs0 n1
     | None -> x)

(** val leq_fin : int -> fin -> fin -> (__, bool) sum **)

let rec leq_fin n0 i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n1 ->
    match Obj.magic i with
    | Some i' ->
      (match Obj.magic j with
       | Some j' ->
         (match leq_fin n1 i' j' with
          | Inl _ -> Inl __
          | Inr b0 -> Inr b0)
       | None -> Inr false)
    | None ->
      (match Obj.magic j with
       | Some _ -> Inr true
       | None -> Inl __))
    n0

type 'x hlist = __

type ('i, 't_) hlist' = 't_ hlist

type 't hlist2 = 't hlist hlist

type ('x0, 'x) hfun = __

type ('i, 't_, 's) hfun' = ('t_, 's) hfun

(** val happ : int -> ('a1, 'a2) hfun -> 'a1 hlist -> 'a2 **)

let rec happ n0 x x0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic x)
    (fun n1 ->
    happ n1 (Obj.magic x (Obj.magic x0).hd) (Obj.magic x0).tl)
    n0

(** val hcurry :
    int -> ('a1 hlist -> 'a2) -> ('a1, 'a2) hfun **)

let rec hcurry n0 x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic x ())
    (fun n1 ->
    Obj.magic (fun x0 ->
      hcurry n1 (fun xs -> Obj.magic x { hd = x0; tl = xs })))
    n0

type ('t, 's) hfun2 = __

(** val happ2 :
    int -> (fin -> int) -> ('a1, 'a2) hfun2 -> 'a1 hlist2 ->
    'a2 **)

let rec happ2 n0 m x x0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic x)
    (fun n1 ->
    happ2 n1 (fun i -> Obj.magic m (Some i))
      (happ (Obj.magic m None) x (Obj.magic x0).hd)
      (Obj.magic x0).tl)
    n0

type ('t, 'x) hdfun = __

(** val hdapp :
    int -> ('a1, 'a2) hdfun -> 'a1 hlist -> 'a2 **)

let rec hdapp n0 x x0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic x)
    (fun n1 ->
    let x1 = (Obj.magic x0).hd in
    let xs = (Obj.magic x0).tl in hdapp n1 (Obj.magic x x1) xs)
    n0

(** val hnth : int -> 'a1 hlist -> fin -> 'a1 **)

let rec hnth n0 x i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n1 ->
    match Obj.magic i with
    | Some j -> hnth n1 (Obj.magic x).tl j
    | None -> (Obj.magic x).hd)
    n0

(** val hlist_of_fun : int -> (fin -> 'a1) -> 'a1 hlist **)

let rec hlist_of_fun n0 f =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n1 ->
    Obj.magic { hd = (Obj.magic f None); tl =
      (hlist_of_fun n1 (fun i -> Obj.magic f (Some i))) })
    n0

(** val hmap :
    int -> (fin -> 'a1 -> 'a2) -> 'a1 hlist -> 'a2 hlist **)

let rec hmap n0 f x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Obj.magic ())
    (fun n1 ->
    Obj.magic { hd = (Obj.magic f None (Obj.magic x).hd);
      tl =
      (hmap n1 (fun j -> Obj.magic f (Some j))
        (Obj.magic x).tl) })
    n0

(** val hmap' :
    ('a1 -> 'a2 -> 'a3) -> 'a1 PolyType.seq -> ('a1, 'a2)
    hlist' -> ('a1, 'a3) hlist' **)

let hmap' f xs =
  hmap (PolyType.size xs) (fun i -> f (nth_fin xs i))

type 'x hlist1' = __

(** val hnth1' : int -> 'a1 hlist1' -> fin -> 'a1 **)

let rec hnth1' m x i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    match Obj.magic i with
    | Some _ -> assert false (* absurd case *)
    | None -> Obj.magic x)
    (fun m0 ->
    match Obj.magic i with
    | Some i0 -> hnth1' m0 (snd (Obj.magic x)) i0
    | None -> fst (Obj.magic x))
    m

type 'x hlist1 = __

(** val hnth1 : int -> 'a1 hlist1 -> fin -> 'a1 **)

let hnth1 m l i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n0 -> hnth1' n0 l i)
    m

type 'r fun_split =
  fin -> 'r
  (* singleton inductive, whose constructor was FunSplit *)

(** val fs_fun :
    int -> 'a1 -> (fin -> 'a1) -> 'a1 fun_split -> fin -> 'a1 **)

let fs_fun _ _ _ f =
  f

(** val fun_split1 : int -> (fin -> 'a1) -> 'a1 fun_split **)

let fun_split1 _ tTs =
  tTs

type arg =
| NonRec
| Rec of fin

type 't type_of_arg = __

(** val type_of_arg_map :
    int -> (fin -> 'a1 -> 'a2) -> arg -> 'a1 type_of_arg ->
    'a2 type_of_arg **)

let type_of_arg_map _ f = function
| NonRec -> (fun x -> x)
| Rec i -> Obj.magic f i

type arity = arg PolyType.seq

type signature = arity PolyType.seq

type declaration = fin -> signature

(** val empty_decl : int -> declaration **)

let empty_decl _ _ =
  PolyType.Coq_nil

(** val add_arity :
    int -> declaration -> fin -> arity -> declaration **)

let add_arity n0 d i as0 j =
  match leq_fin n0 i j with
  | Inl _ -> PolyType.Coq_cons (as0, (d i))
  | Inr _ -> d j

(** val add_arity_ind :
    int -> (fin -> arity PolyType.seq) -> fin -> arity -> fin
    -> 'a1 -> 'a1 -> 'a1 **)

let add_arity_ind n0 _ i _ j h1 h2 =
  match leq_fin n0 i j with
  | Inl _ -> cast i j h1
  | Inr _ -> h2

type ('k, 'sort) arg_class = __

type ('k, 'sort) arg_inst = { arg_inst_sort : arg;
                              arg_inst_class : ('k, 'sort)
                                               arg_class }

type ('k, 'sort) arity_class =
  (arg, ('k, 'sort) arg_class) hlist'

type ('k, 'sort) arity_inst = { arity_inst_sort : arity;
                                arity_inst_class : ('k,
                                                   'sort)
                                                   arity_class }

type ('k, 'sort) sig_class =
  (arity, ('k, 'sort) arity_class) hlist'

type ('k, 'sort) sig_inst = { sig_inst_sort : signature;
                              sig_inst_class : ('k, 'sort)
                                               sig_class }

type tagged_decl =
  fin -> signature
  (* singleton inductive, whose constructor was TaggedDecl *)

(** val untag_decl :
    int -> int -> tagged_decl -> fin -> signature **)

let untag_decl _ _ t =
  t

type ('k, 'sort) decl_inst = { decl_inst_sort : tagged_decl;
                               decl_inst__1 : (fin -> ('k,
                                              'sort)
                                              sig_class) }

(** val decl_inst_class :
    int -> int -> ('a1, 'a2) decl_inst -> fin -> ('a1, 'a2)
    sig_class **)

let decl_inst_class _ _ d =
  d.decl_inst__1

(** val nonRec_arg_inst :
    int -> 'a1 -> ('a1, 'a2) arg_inst **)

let nonRec_arg_inst _ sX =
  { arg_inst_sort = NonRec; arg_inst_class = (Obj.magic sX) }

(** val rec_arg_inst : int -> fin -> ('a1, 'a2) arg_inst **)

let rec_arg_inst _ i =
  { arg_inst_sort = (Rec i); arg_inst_class = (Obj.magic ()) }

(** val nil_arity_inst : int -> ('a1, 'a2) arity_inst **)

let nil_arity_inst _ =
  { arity_inst_sort = PolyType.Coq_nil; arity_inst_class =
    (Obj.magic ()) }

(** val cons_arity_inst :
    int -> ('a1, 'a2) arg_inst -> ('a1, 'a2) arity_inst ->
    ('a1, 'a2) arity_inst **)

let cons_arity_inst _ ai asi =
  { arity_inst_sort = (PolyType.Coq_cons (ai.arg_inst_sort,
    asi.arity_inst_sort)); arity_inst_class =
    (Obj.magic { hd = ai.arg_inst_class; tl =
      asi.arity_inst_class }) }

(** val nil_sig_inst : int -> ('a1, 'a2) sig_inst **)

let nil_sig_inst _ =
  { sig_inst_sort = PolyType.Coq_nil; sig_inst_class =
    (Obj.magic ()) }

(** val cons_sig_inst :
    int -> ('a1, 'a2) arity_inst -> ('a1, 'a2) sig_inst ->
    ('a1, 'a2) sig_inst **)

let cons_sig_inst _ asi _UU03a3_i =
  { sig_inst_sort = (PolyType.Coq_cons (asi.arity_inst_sort,
    _UU03a3_i.sig_inst_sort)); sig_inst_class =
    (Obj.magic { hd = asi.arity_inst_class; tl =
      _UU03a3_i.sig_inst_class }) }

(** val nil_decl_tag :
    int -> int -> (fin -> signature) -> tagged_decl **)

let nil_decl_tag _ _ d =
  d

(** val cons_decl_tag :
    int -> int -> (fin -> signature) -> tagged_decl **)

let cons_decl_tag =
  nil_decl_tag

(** val nil_decl_inst :
    int -> (fin -> signature) -> ('a1, 'a2) decl_inst **)

let nil_decl_inst n0 f =
  { decl_inst_sort = (nil_decl_tag n0 0 f); decl_inst__1 =
    (fun _ -> assert false (* absurd case *)) }

(** val cons_decl_inst :
    int -> int -> ('a1, 'a2) sig_inst -> ('a1, 'a2) decl_inst
    -> signature fun_split -> ('a1, 'a2) decl_inst **)

let cons_decl_inst n0 k _UU03a3_i di d =
  { decl_inst_sort =
    (cons_decl_tag n0 (Stdlib.Int.succ k)
      (fs_fun k _UU03a3_i.sig_inst_sort
        (untag_decl n0 k di.decl_inst_sort) d));
    decl_inst__1 = (fun i ->
    match Obj.magic i with
    | Some i0 ->
      cast (untag_decl n0 k di.decl_inst_sort i0)
        (fs_fun k _UU03a3_i.sig_inst_sort
          (untag_decl n0 k di.decl_inst_sort) d
          (Obj.magic (Some i0))) (decl_inst_class n0 k di i0)
    | None ->
      cast _UU03a3_i.sig_inst_sort
        (fs_fun k _UU03a3_i.sig_inst_sort
          (untag_decl n0 k di.decl_inst_sort) d
          (Obj.magic None)) _UU03a3_i.sig_inst_class) }

(** val arity_rec :
    int -> 'a3 -> ('a1 -> arity -> 'a3 -> 'a3) -> (fin ->
    arity -> 'a3 -> 'a3) -> arity -> ('a1, 'a2) arity_class
    -> 'a3 **)

let rec arity_rec n0 pnil pNonRec pRec as0 cAs =
  match as0 with
  | PolyType.Coq_nil -> pnil
  | PolyType.Coq_cons (a0, as1) ->
    (match a0 with
     | NonRec ->
       cast __ __
         (pNonRec (PolyType.sval (Obj.magic cAs).hd) as1
           (arity_rec n0 pnil pNonRec pRec as1
             (Obj.magic cAs).tl))
     | Rec i ->
       pRec i as1
         (arity_rec n0 pnil pNonRec pRec as1
           (Obj.magic cAs).tl))

module Ind =
 struct
  type coq_Cidx = fin

  type 't constructors =
    fin -> coq_Cidx -> (arg, 't type_of_arg, 't) hfun'

  (** val empty_cons : int -> 'a1 constructors **)

  let empty_cons _ _ _ =
    assert false (* absurd case *)

  (** val add_cons :
      int -> declaration -> 'a1 constructors -> fin -> arity
      -> (arg, 'a1 type_of_arg, 'a1) hfun' -> 'a1 constructors **)

  let add_cons n0 d cs ti as0 c ti' =
    add_arity_ind n0 d ti as0 ti' (fun ci ->
      match Obj.magic ci with
      | Some ci0 -> cs ti ci0
      | None -> c) (cs ti')

  type ('t, 's) rec_branch' = __

  type ('t, 's) rec_branch = ('t, 's) rec_branch'

  type 't recursor =
    __ -> (('t, __) rec_branch, ('t -> __) hlist1) hfun2

  (** val rec_branch'_of_hfun' :
      int -> fin -> arity -> (arg, ('a1 * 'a2) type_of_arg,
      'a2) hfun' -> ('a1, 'a2) rec_branch' **)

  let rec rec_branch'_of_hfun' n0 i as0 x =
    match as0 with
    | PolyType.Coq_nil -> x
    | PolyType.Coq_cons (a0, as1) ->
      (match a0 with
       | NonRec ->
         Obj.magic (fun x0 ->
           rec_branch'_of_hfun' n0 i as1 (Obj.magic x x0))
       | Rec _ ->
         Obj.magic (fun x0 y ->
           rec_branch'_of_hfun' n0 i as1 (Obj.magic x (x0, y))))

  type ('t, 's) des_branch = (arg, 't type_of_arg, 's) hfun'

  type 't destructor =
    __ -> (('t, __) des_branch, ('t -> __) hlist1) hfun2

  type ('t, 'p) ind_branch' = __

  type ('t, 'p) ind_branch = ('t, 'p) ind_branch'

  type 't induction =
    (__, (('t, __) ind_branch, ('t -> __) hlist1) hfun2) hdfun

  module Def =
   struct
    type 'sorts class_of = { coq_Cons : 'sorts constructors;
                             coq_rec : 'sorts recursor;
                             case : 'sorts destructor;
                             indP : 'sorts induction }

    (** val coq_Cons :
        int -> declaration -> 'a1 class_of -> 'a1 constructors **)

    let coq_Cons _ _ c =
      c.coq_Cons

    (** val coq_rec :
        int -> declaration -> 'a1 class_of -> (('a1, __)
        rec_branch, ('a1 -> __) hlist1) hfun2 **)

    let coq_rec _ _ c =
      c.coq_rec __

    (** val case :
        int -> declaration -> 'a1 class_of -> (('a1, __)
        des_branch, ('a1 -> __) hlist1) hfun2 **)

    let case _ _ c =
      c.case __

    (** val indP :
        int -> declaration -> 'a1 class_of -> 'a1 induction **)

    let indP _ _ c =
      c.indP

    type coq_type = { n : int; decl : declaration;
                      coq_class : __ class_of }

    (** val n : coq_type -> int **)

    let n t =
      t.n

    (** val decl : coq_type -> declaration **)

    let decl t =
      t.decl

    (** val coq_class : coq_type -> __ class_of **)

    let coq_class t =
      t.coq_class
   end

  type 't mixin_of = { def : Def.coq_type; idx : fin }

  (** val def : 'a1 mixin_of -> Def.coq_type **)

  let def m =
    m.def

  (** val idx : 'a1 mixin_of -> fin **)

  let idx m =
    m.idx

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

module IndF =
 struct
  type 't fobj = { constr : Ind.coq_Cidx;
                   args : (arg, 't type_of_arg) hlist' }

  (** val constr :
      int -> declaration -> fin -> 'a1 fobj -> Ind.coq_Cidx **)

  let constr _ _ _ f =
    f.constr

  (** val args :
      int -> declaration -> fin -> 'a1 fobj -> (arg, 'a1
      type_of_arg) hlist' **)

  let args _ _ _ f =
    f.args

  (** val fmap :
      int -> declaration -> (fin -> 'a1 -> 'a2) -> fin -> 'a1
      fobj -> 'a2 fobj **)

  let fmap n0 d f i x =
    { constr = x.constr; args =
      (hmap' (type_of_arg_map n0 f) (nth_fin (d i) x.constr)
        x.args) }

  (** val coq_Roll :
      Ind.Def.coq_type -> fin -> __ fobj -> __ **)

  let coq_Roll t i x =
    happ
      (PolyType.size (nth_fin (t.Ind.Def.decl i) x.constr))
      (t.Ind.Def.coq_class.Ind.Def.coq_Cons i x.constr) x.args

  (** val rec_branches_of_fun :
      Ind.Def.coq_type -> (fin -> (__ * 'a1) fobj -> 'a1) ->
      (__, 'a1) Ind.rec_branch hlist2 **)

  let rec_branches_of_fun t body0 =
    hlist_of_fun t.Ind.Def.n (fun i ->
      hlist_of_fun (PolyType.size (t.Ind.Def.decl i))
        (fun j ->
        Ind.rec_branch'_of_hfun' t.Ind.Def.n i
          (nth_fin (t.Ind.Def.decl i) j)
          (hcurry
            (PolyType.size (nth_fin (t.Ind.Def.decl i) j))
            (fun l -> body0 i { constr = j; args = l }))))

  (** val coq_rec :
      Ind.Def.coq_type -> (fin -> (__ * 'a1) fobj -> 'a1) ->
      (__ -> 'a1) hlist1 **)

  let coq_rec t body0 =
    happ2 t.Ind.Def.n (fun i ->
      PolyType.size (t.Ind.Def.decl i))
      (Ind.Def.coq_rec t.Ind.Def.n t.Ind.Def.decl
        t.Ind.Def.coq_class) (rec_branches_of_fun t body0)

  type 'r lift_type = __

  (** val lift_type_of :
      Ind.Def.coq_type -> fin -> fin -> (__ -> 'a1) -> 'a1
      lift_type **)

  let lift_type_of t i j f =
    match leq_fin t.Ind.Def.n i j with
    | Inl _ -> Obj.magic f __
    | Inr _ -> Obj.magic ()

  (** val des_branches_of_fun :
      Ind.Def.coq_type -> fin -> (__ fobj -> 'a1) -> (__, 'a1
      lift_type) Ind.des_branch hlist2 **)

  let des_branches_of_fun t i body0 =
    hlist_of_fun t.Ind.Def.n (fun i' ->
      hlist_of_fun (PolyType.size (t.Ind.Def.decl i'))
        (fun j ->
        hcurry
          (PolyType.size (nth_fin (t.Ind.Def.decl i') j))
          (fun l ->
          lift_type_of t i i' (fun _ ->
            body0 (cast i' i { constr = j; args = l })))))

  (** val case :
      Ind.Def.coq_type -> fin -> (__ fobj -> 'a1) -> __ -> 'a1 **)

  let case t i body0 x =
    cast __ __
      (hnth1 t.Ind.Def.n
        (happ2 t.Ind.Def.n (fun i0 ->
          PolyType.size (t.Ind.Def.decl i0))
          (Ind.Def.case t.Ind.Def.n t.Ind.Def.decl
            t.Ind.Def.coq_class)
          (des_branches_of_fun t i body0)) i x)

  (** val indP :
      Ind.Def.coq_type -> (fin -> (__, 'a1) sigT fobj -> 'a1)
      -> fin -> __ -> 'a1 **)

  let indP t iH =
    let q = hlist_of_fun t.Ind.Def.n (Obj.magic __) in
    let q_of_P = fun _ _ -> cast __ __ in
    let p_of_Q = fun _ _ -> cast __ __ in
    let tP_of_TQ = fun i x ->
      tagged0 (tag x) (p_of_Q i (tag x) (tagged x))
    in
    let iH0 = fun i a0 ->
      q_of_P i
        (coq_Roll t i
          (fmap t.Ind.Def.n t.Ind.Def.decl (fun _ -> tag) i
            (fmap t.Ind.Def.n t.Ind.Def.decl tP_of_TQ i a0)))
        (iH i (fmap t.Ind.Def.n t.Ind.Def.decl tP_of_TQ i a0))
    in
    (fun i x ->
    p_of_Q i x
      (let n0 = t.Ind.Def.n in
       let d = t.Ind.Def.decl in
       let __top_assumption_ = t.Ind.Def.coq_class in
       let cs = __top_assumption_.Ind.Def.coq_Cons in
       let indP0 = __top_assumption_.Ind.Def.indP in
       let hyps = fun i0 j ->
         let hyps = fun args0 ->
           iH0 i0 { constr = j; args = args0 }
         in
         let _evar_0_ = fun _ _view_subject_ ->
           _view_subject_ ()
         in
         let _evar_0_0 = fun __top_assumption_0 ->
           let _evar_0_0 = fun _ iH1 c hyps0 x0 ->
             iH1 (c x0) (fun args0 ->
               hyps0 { hd = x0; tl = args0 })
           in
           let _evar_0_1 = fun _ _ iH1 constr0 hyps0 x0 h ->
             iH1 (constr0 x0) (fun args0 ->
               hyps0 { hd = (ExistT (x0, h)); tl = args0 })
           in
           (match __top_assumption_0 with
            | NonRec -> _evar_0_0
            | Rec f -> Obj.magic _evar_0_1 f)
         in
         let rec f = function
         | PolyType.Coq_nil -> Obj.magic _evar_0_
         | PolyType.Coq_cons (y, s0) ->
           Obj.magic _evar_0_0 y s0 (f s0)
         in f (nth_fin (d i0) j) (cs i0 j) hyps
       in
       let bs =
         hlist_of_fun n0 (fun i0 ->
           hlist_of_fun (PolyType.size (d i0)) (fun j ->
             hyps i0 j))
       in
       hnth1 n0
         (happ2 n0 (fun i0 -> PolyType.size (d i0))
           (hdapp n0 indP0 q) bs) i x))

  (** val unroll :
      Ind.Def.coq_type -> fin -> __ -> __ fobj **)

  let unroll t i =
    case t i (fun x -> x)
 end

module DerEqType =
 struct
  (** val eq_op_branch :
      Ind.Def.coq_type -> arg PolyType.seq -> (arg,
      (Equality.coq_type, Equality.sort) arg_class) hlist' ->
      (arg, (__ * (__ -> bool)) type_of_arg) hlist' -> (arg,
      __ type_of_arg) hlist' -> bool -> bool **)

  let eq_op_branch t as0 cAs =
    arity_rec t.Ind.Def.n (fun _ _ b0 -> b0)
      (fun r _ rec0 x y b0 ->
      rec0 (Obj.magic x).tl (Obj.magic y).tl
        ((&&) b0 (eq_op0 r (Obj.magic x).hd (Obj.magic y).hd)))
      (fun _ _ rec0 x y b0 ->
      rec0 (Obj.magic x).tl (Obj.magic y).tl
        ((&&) b0 (snd (Obj.magic x).hd (Obj.magic y).hd)))
      as0 cAs

  (** val eq_op :
      Ind.Def.coq_type -> (fin -> (Equality.coq_type,
      Equality.sort) sig_class) -> fin -> __ -> __ -> bool **)

  let eq_op t sT =
    hnth1 t.Ind.Def.n
      (IndF.coq_rec t (fun i args1 ->
        IndF.case t i (fun args2 ->
          match leq_fin (PolyType.size (t.Ind.Def.decl i))
                  args2.IndF.constr args1.IndF.constr with
          | Inl _ ->
            eq_op_branch t
              (nth_fin (t.Ind.Def.decl i) args1.IndF.constr)
              (hnth (PolyType.size (t.Ind.Def.decl i)) 
                (sT i) args1.IndF.constr) args1.IndF.args
              (cast args2.IndF.constr args1.IndF.constr
                args2.IndF.args) true
          | Inr _ -> false)))

  (** val eq_opP :
      Ind.Def.coq_type -> (fin -> (Equality.coq_type,
      Equality.sort) sig_class) -> fin -> __ eq_axiom **)

  let eq_opP t sT i _top_assumption_ =
    let _evar_0_ = fun i0 __top_assumption_ ->
      let _evar_0_ = fun xC xargs y ->
        let __top_assumption_0 = IndF.unroll t i0 y in
        let _evar_0_ = fun yC yargs ->
          let _evar_0_ = fun _ _ ->
            let _evar_0_ =
              iffP
                (eq_op_branch t
                  (nth_fin (t.Ind.Def.decl i0) yC)
                  (hnth (PolyType.size (t.Ind.Def.decl i0))
                    (sT i0) yC)
                  (hmap'
                    (type_of_arg_map t.Ind.Def.n (fun j x ->
                      (x, (eq_op t sT j x))))
                    (nth_fin (t.Ind.Def.decl i0) yC)
                    (hmap'
                      (type_of_arg_map t.Ind.Def.n (fun _ ->
                        tag))
                      (nth_fin (t.Ind.Def.decl i0) yC) xargs))
                  yargs true)
                (idP
                  (eq_op_branch t
                    (nth_fin (t.Ind.Def.decl i0) yC)
                    (hnth (PolyType.size (t.Ind.Def.decl i0))
                      (sT i0) yC)
                    (hmap'
                      (type_of_arg_map t.Ind.Def.n
                        (fun j x -> (x, (eq_op t sT j x))))
                      (nth_fin (t.Ind.Def.decl i0) yC)
                      (hmap'
                        (type_of_arg_map t.Ind.Def.n
                          (fun _ -> tag))
                        (nth_fin (t.Ind.Def.decl i0) yC)
                        xargs)) yargs true))
            in
            iffP
              (eq_op_branch t
                (nth_fin (t.Ind.Def.decl i0) yC)
                (hnth (PolyType.size (t.Ind.Def.decl i0))
                  (sT i0) yC)
                (hmap'
                  (type_of_arg_map t.Ind.Def.n (fun j x ->
                    (x, (eq_op t sT j x))))
                  (nth_fin (t.Ind.Def.decl i0) yC)
                  (hmap'
                    (type_of_arg_map t.Ind.Def.n (fun _ ->
                      tag)) (nth_fin (t.Ind.Def.decl i0) yC)
                    xargs)) yargs true) _evar_0_
          in
          let _evar_0_0 = fun _ -> ReflectF in
          (match leq_fin (PolyType.size (t.Ind.Def.decl i0))
                   yC xC with
           | Inl _ -> _evar_0_ __ __
           | Inr b0 -> _evar_0_0 b0)
        in
        let { IndF.constr = constr0; IndF.args = args0 } =
          __top_assumption_0
        in
        _evar_0_ constr0 args0
      in
      let { IndF.constr = constr0; IndF.args = args0 } =
        __top_assumption_
      in
      _evar_0_ constr0 args0
    in
    IndF.indP t _evar_0_ i _top_assumption_
 end

type regex =
| Eps
| Empt
| Event of Equality.sort
| Plus of regex * regex
| Seq of regex * regex
| Star of regex

(** val regex_hasDecEq :
    Equality.coq_type -> regex Coq_hasDecEq.axioms_ **)

let regex_hasDecEq a0 =
  { Coq_hasDecEq.eq_op =
    (let rec f r x =
       match r with
       | Eps -> (match x with
                 | Eps -> true
                 | _ -> false)
       | Empt -> (match x with
                  | Empt -> true
                  | _ -> false)
       | Event s ->
         (match x with
          | Event s0 -> (&&) true (eq_op0 a0 s s0)
          | _ -> false)
       | Plus (r0, r1) ->
         (match x with
          | Plus (r2, r3) ->
            (&&) ((&&) true (f r0 r2)) (f r1 r3)
          | _ -> false)
       | Seq (r0, r1) ->
         (match x with
          | Seq (r2, r3) ->
            (&&) ((&&) true (f r0 r2)) (f r1 r3)
          | _ -> false)
       | Star r0 ->
         (match x with
          | Star r1 -> (&&) true (f r0 r1)
          | _ -> false)
     in f); Coq_hasDecEq.eqP =
    (Obj.magic DerEqType.eq_opP
      (Ind.coq_class { Ind.def = { Ind.Def.n =
        (Stdlib.Int.succ 0); Ind.Def.decl =
        (add_arity (Stdlib.Int.succ 0)
          (add_arity (Stdlib.Int.succ 0)
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil))) (Obj.magic None)
            PolyType.Coq_nil) (Obj.magic None)
          PolyType.Coq_nil); Ind.Def.coq_class =
        { Ind.Def.coq_Cons =
        (Ind.add_cons (Stdlib.Int.succ 0)
          (add_arity (Stdlib.Int.succ 0)
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil))) (Obj.magic None)
            PolyType.Coq_nil)
          (Ind.add_cons (Stdlib.Int.succ 0)
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil)))
            (Ind.add_cons (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Ind.add_cons (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Ind.add_cons (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Ind.add_cons (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Ind.empty_cons (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil))
                    (Obj.magic (fun x -> Star x)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil))))
                  (Obj.magic (fun x x0 -> Seq (x, x0))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil))))
                (Obj.magic (fun x x0 -> Plus (x, x0))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil))
              (Obj.magic (fun x -> Event x)))
            (Obj.magic None) PolyType.Coq_nil
            (Obj.magic Empt)) (Obj.magic None)
          PolyType.Coq_nil (Obj.magic Eps));
        Ind.Def.coq_rec = (fun _ ->
        Obj.magic (fun f f0 f1 f2 f3 f4 ->
          let rec f5 = function
          | Eps -> f
          | Empt -> f0
          | Event s -> f1 s
          | Plus (r0, r1) -> f2 r0 (f5 r0) r1 (f5 r1)
          | Seq (r0, r1) -> f3 r0 (f5 r0) r1 (f5 r1)
          | Star r0 -> f4 r0 (f5 r0)
          in f5)); Ind.Def.case = (fun _ ->
        Obj.magic (fun x x0 x1 x2 x3 x4 r ->
          match r with
          | Eps -> x
          | Empt -> x0
          | Event s -> x1 s
          | Plus (r0, r1) -> x2 r0 r1
          | Seq (r0, r1) -> x3 r0 r1
          | Star r0 -> x4 r0)); Ind.Def.indP =
        (Obj.magic (fun _ f f0 f1 f2 f3 f4 ->
          let rec f5 = function
          | Eps -> f
          | Empt -> f0
          | Event s -> f1 s
          | Plus (r0, r1) -> f2 r0 (f5 r0) r1 (f5 r1)
          | Seq (r0, r1) -> f3 r0 (f5 r0) r1 (f5 r1)
          | Star r0 -> f4 r0 (f5 r0)
          in f5)) } }; Ind.idx = (Obj.magic None) }).Ind.def
      (decl_inst_class (Stdlib.Int.succ 0) (Stdlib.Int.succ
        0)
        (cons_decl_inst (Stdlib.Int.succ 0) 0
          (cons_sig_inst (Stdlib.Int.succ 0)
            (nil_arity_inst (Stdlib.Int.succ 0))
            (cons_sig_inst (Stdlib.Int.succ 0)
              (nil_arity_inst (Stdlib.Int.succ 0))
              (cons_sig_inst (Stdlib.Int.succ 0)
                (cons_arity_inst (Stdlib.Int.succ 0)
                  (nonRec_arg_inst (Stdlib.Int.succ 0) a0)
                  (nil_arity_inst (Stdlib.Int.succ 0)))
                (cons_sig_inst (Stdlib.Int.succ 0)
                  (cons_arity_inst (Stdlib.Int.succ 0)
                    (rec_arg_inst (Stdlib.Int.succ 0)
                      (Obj.magic None))
                    (cons_arity_inst (Stdlib.Int.succ 0)
                      (rec_arg_inst (Stdlib.Int.succ 0)
                        (Obj.magic None))
                      (nil_arity_inst (Stdlib.Int.succ 0))))
                  (cons_sig_inst (Stdlib.Int.succ 0)
                    (cons_arity_inst (Stdlib.Int.succ 0)
                      (rec_arg_inst (Stdlib.Int.succ 0)
                        (Obj.magic None))
                      (cons_arity_inst (Stdlib.Int.succ 0)
                        (rec_arg_inst (Stdlib.Int.succ 0)
                          (Obj.magic None))
                        (nil_arity_inst (Stdlib.Int.succ 0))))
                    (cons_sig_inst (Stdlib.Int.succ 0)
                      (cons_arity_inst (Stdlib.Int.succ 0)
                        (rec_arg_inst (Stdlib.Int.succ 0)
                          (Obj.magic None))
                        (nil_arity_inst (Stdlib.Int.succ 0)))
                      (nil_sig_inst (Stdlib.Int.succ 0))))))))
          (nil_decl_inst (Stdlib.Int.succ 0) (fun i ->
            add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (add_arity (Stdlib.Int.succ 0)
                      (add_arity (Stdlib.Int.succ 0)
                        (empty_decl (Stdlib.Int.succ 0))
                        (Obj.magic None) (PolyType.Coq_cons
                        ((Rec (Obj.magic None)),
                        PolyType.Coq_nil))) (Obj.magic None)
                      (PolyType.Coq_cons ((Rec
                      (Obj.magic None)), (PolyType.Coq_cons
                      ((Rec (Obj.magic None)),
                      PolyType.Coq_nil))))) (Obj.magic None)
                    (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), (PolyType.Coq_cons
                    ((Rec (Obj.magic None)),
                    PolyType.Coq_nil))))) (Obj.magic None)
                  (PolyType.Coq_cons (NonRec,
                  PolyType.Coq_nil))) (Obj.magic None)
                PolyType.Coq_nil) (Obj.magic None)
              PolyType.Coq_nil (Obj.magic (Some i))))
          (fun_split1 0
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (add_arity (Stdlib.Int.succ 0)
                      (add_arity (Stdlib.Int.succ 0)
                        (empty_decl (Stdlib.Int.succ 0))
                        (Obj.magic None) (PolyType.Coq_cons
                        ((Rec (Obj.magic None)),
                        PolyType.Coq_nil))) (Obj.magic None)
                      (PolyType.Coq_cons ((Rec
                      (Obj.magic None)), (PolyType.Coq_cons
                      ((Rec (Obj.magic None)),
                      PolyType.Coq_nil))))) (Obj.magic None)
                    (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), (PolyType.Coq_cons
                    ((Rec (Obj.magic None)),
                    PolyType.Coq_nil))))) (Obj.magic None)
                  (PolyType.Coq_cons (NonRec,
                  PolyType.Coq_nil))) (Obj.magic None)
                PolyType.Coq_nil) (Obj.magic None)
              PolyType.Coq_nil))))
      (Ind.coq_class { Ind.def = { Ind.Def.n =
        (Stdlib.Int.succ 0); Ind.Def.decl =
        (add_arity (Stdlib.Int.succ 0)
          (add_arity (Stdlib.Int.succ 0)
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil))) (Obj.magic None)
            PolyType.Coq_nil) (Obj.magic None)
          PolyType.Coq_nil); Ind.Def.coq_class =
        { Ind.Def.coq_Cons =
        (Ind.add_cons (Stdlib.Int.succ 0)
          (add_arity (Stdlib.Int.succ 0)
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil))) (Obj.magic None)
            PolyType.Coq_nil)
          (Ind.add_cons (Stdlib.Int.succ 0)
            (add_arity (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil)))
            (Ind.add_cons (Stdlib.Int.succ 0)
              (add_arity (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil)))))
              (Ind.add_cons (Stdlib.Int.succ 0)
                (add_arity (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil)))))
                (Ind.add_cons (Stdlib.Int.succ 0)
                  (add_arity (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil)))
                  (Ind.add_cons (Stdlib.Int.succ 0)
                    (empty_decl (Stdlib.Int.succ 0))
                    (Ind.empty_cons (Stdlib.Int.succ 0))
                    (Obj.magic None) (PolyType.Coq_cons ((Rec
                    (Obj.magic None)), PolyType.Coq_nil))
                    (Obj.magic (fun x -> Star x)))
                  (Obj.magic None) (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), (PolyType.Coq_cons ((Rec
                  (Obj.magic None)), PolyType.Coq_nil))))
                  (Obj.magic (fun x x0 -> Seq (x, x0))))
                (Obj.magic None) (PolyType.Coq_cons ((Rec
                (Obj.magic None)), (PolyType.Coq_cons ((Rec
                (Obj.magic None)), PolyType.Coq_nil))))
                (Obj.magic (fun x x0 -> Plus (x, x0))))
              (Obj.magic None) (PolyType.Coq_cons (NonRec,
              PolyType.Coq_nil))
              (Obj.magic (fun x -> Event x)))
            (Obj.magic None) PolyType.Coq_nil
            (Obj.magic Empt)) (Obj.magic None)
          PolyType.Coq_nil (Obj.magic Eps));
        Ind.Def.coq_rec = (fun _ ->
        Obj.magic (fun f f0 f1 f2 f3 f4 ->
          let rec f5 = function
          | Eps -> f
          | Empt -> f0
          | Event s -> f1 s
          | Plus (r0, r1) -> f2 r0 (f5 r0) r1 (f5 r1)
          | Seq (r0, r1) -> f3 r0 (f5 r0) r1 (f5 r1)
          | Star r0 -> f4 r0 (f5 r0)
          in f5)); Ind.Def.case = (fun _ ->
        Obj.magic (fun x x0 x1 x2 x3 x4 r ->
          match r with
          | Eps -> x
          | Empt -> x0
          | Event s -> x1 s
          | Plus (r0, r1) -> x2 r0 r1
          | Seq (r0, r1) -> x3 r0 r1
          | Star r0 -> x4 r0)); Ind.Def.indP =
        (Obj.magic (fun _ f f0 f1 f2 f3 f4 ->
          let rec f5 = function
          | Eps -> f
          | Empt -> f0
          | Event s -> f1 s
          | Plus (r0, r1) -> f2 r0 (f5 r0) r1 (f5 r1)
          | Seq (r0, r1) -> f3 r0 (f5 r0) r1 (f5 r1)
          | Star r0 -> f4 r0 (f5 r0)
          in f5)) } }; Ind.idx = (Obj.magic None) }).Ind.idx) }

(** val hB_unnamed_factory_2 :
    Equality.coq_type -> regex Coq_hasDecEq.axioms_ **)

let hB_unnamed_factory_2 =
  regex_hasDecEq

(** val regex_regex__canonical__eqtype_Equality :
    Equality.coq_type -> Equality.coq_type **)

let regex_regex__canonical__eqtype_Equality a0 =
  Obj.magic hB_unnamed_factory_2 a0

(** val nu : Equality.coq_type -> regex -> bool **)

let rec nu a0 = function
| Eps -> true
| Plus (c0, c1) -> (||) (nu a0 c0) (nu a0 c1)
| Seq (c0, c1) -> (&&) (nu a0 c0) (nu a0 c1)
| Star _ -> true
| _ -> false

(** val derive :
    Equality.coq_type -> Equality.sort -> regex -> regex **)

let rec derive a0 e = function
| Event e' -> if eq_op0 a0 e' e then Eps else Empt
| Plus (c0, c1) -> Plus ((derive a0 e c0), (derive a0 e c1))
| Seq (c0, c1) ->
  if nu a0 c0
  then Plus ((Seq ((derive a0 e c0), c1)), (derive a0 e c1))
  else Seq ((derive a0 e c0), c1)
| Star c0 -> Seq ((derive a0 e c0), (Star c0))
| _ -> Empt

(** val pd :
    Equality.coq_type -> Equality.sort -> regex -> regex list **)

let rec pd a0 a1 = function
| Event a' -> if eq_op0 a0 a1 a' then Eps :: [] else []
| Plus (r0, r1) -> cat (pd a0 a1 r0) (pd a0 a1 r1)
| Seq (r0, r1) ->
  if nu a0 r0
  then cat (map (fun x -> Seq (x, r1)) (pd a0 a1 r0))
         (pd a0 a1 r1)
  else map (fun x -> Seq (x, r1)) (pd a0 a1 r0)
| Star r0 -> map (fun x -> Seq (x, (Star r0))) (pd a0 a1 r0)
| _ -> []

(** val pd_l :
    Equality.coq_type -> Equality.sort -> regex list ->
    Equality.sort list **)

let pd_l a0 a1 l =
  undup (regex_regex__canonical__eqtype_Equality a0)
    (flatten (map (Obj.magic pd a0 a1) l))

type pder = regex list

(** val o : Equality.coq_type -> regex -> regex **)

let o a0 c =
  if nu a0 c then Eps else Empt

(** val o_l : Equality.coq_type -> pder -> regex **)

let o_l a0 l =
  if has (nu a0) l then Eps else Empt

type pTree =
| P_tt
| P_singl of Equality.sort
| P_inl of regex * regex * pTree
| P_inr of regex * regex * pTree
| P_pair of regex * regex * pTree * pTree
| P_fold of regex * pTree

(** val pTree_1size :
    Equality.coq_type -> regex -> pTree -> int **)

let rec pTree_1size a0 _ = function
| P_inl (r0, _, p0) -> pTree_1size a0 r0 p0
| P_inr (_, r1, p1) -> pTree_1size a0 r1 p1
| P_pair (r0, r1, p0, p1) ->
  addn (pTree_1size a0 r0 p0) (pTree_1size a0 r1 p1)
| P_fold (r0, p0) ->
  pTree_1size a0 (Plus (Eps, (Seq (r0, (Star r0))))) p0
| _ -> Stdlib.Int.succ 0

(** val pTree_0size_rect :
    Equality.coq_type -> regex -> (pTree -> (pTree -> __ ->
    'a1) -> 'a1) -> pTree -> 'a1 **)

let rec pTree_0size_rect a0 r hsize u =
  let _evar_0_ = fun u' -> pTree_0size_rect a0 r hsize u' in
  hsize u (fun u' _ -> _evar_0_ u')

(** val pTree_1size_rect :
    Equality.coq_type -> regex -> (pTree -> (pTree -> __ ->
    'a1) -> 'a1) -> pTree -> 'a1 **)

let rec pTree_1size_rect a0 r hsize u =
  let _evar_0_ = fun u' -> pTree_1size_rect a0 r hsize u' in
  hsize u (fun u' _ -> _evar_0_ u')

type post = pTree

(** val pTree_case :
    Equality.coq_type -> regex -> (__ -> 'a1) ->
    (Equality.sort -> __ -> 'a1) -> (regex -> regex -> __ ->
    pTree -> 'a1) -> (regex -> regex -> __ -> pTree -> 'a1)
    -> (regex -> regex -> __ -> pTree -> pTree -> 'a1) ->
    (regex -> __ -> pTree -> 'a1) -> pTree -> 'a1 **)

let pTree_case _ _ x x0 x1 x2 x3 x4 = function
| P_tt -> x __
| P_singl a0 -> x0 a0 __
| P_inl (r0, r1, p0) -> x1 r0 r1 __ p0
| P_inr (r0, r1, p0) -> x2 r0 r1 __ p0
| P_pair (r0, r1, p0, p1) -> x3 r0 r1 __ p0 p1
| P_fold (r, p0) -> x4 r __ p0

(** val pair_pd_l :
    Finite.coq_type -> Equality.sort -> (pder * pder) ->
    Equality.sort list * Equality.sort list **)

let pair_pd_l a0 a1 pp =
  ((pd_l
     (Finite.Exports.fintype_Finite__to__eqtype_Equality a0)
     a1 (fst pp)),
    (pd_l
      (Finite.Exports.fintype_Finite__to__eqtype_Equality a0)
      a1 (snd pp)))

type vType = (pder * pder) list

type nType = pder * pder

(** val reachable :
    Finite.coq_type -> vType -> nType -> (pder -> pder ->
    bool) -> bool **)

let rec reachable a0 v p p0 =
  if sumbool_of_bool
       (in_mem (Obj.magic p)
         (mem
           (seq_predType
             (datatypes_prod__canonical__eqtype_Equality
               (datatypes_list__canonical__eqtype_Equality
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     a0)))
               (datatypes_list__canonical__eqtype_Equality
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     a0))))) (Obj.magic v)))
  then true
  else (&&) (p0 (fst p) (snd p))
         (all (fun a1 ->
           Obj.magic reachable a0 (p :: v)
             (Obj.magic pair_pd_l a0 a1 p) p0)
           (index_enum a0))

(** val reachable_wrap :
    Finite.coq_type -> pder -> pder -> (pder -> pder -> bool)
    -> bool **)

let reachable_wrap a0 l0 l1 p =
  reachable a0 []
    ((Obj.magic undup
       (regex_regex__canonical__eqtype_Equality
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           a0)) l0),
    (Obj.magic undup
      (regex_regex__canonical__eqtype_Equality
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          a0)) l1)) p

type dsl =
| Shuffle of regex * regex * regex
| Shuffleinv of regex * regex * regex
| Retag of regex * regex
| UntagL of regex
| UntagLinv of regex
| Untag of regex
| TagL of regex * regex
| Assoc of regex * regex * regex
| Associnv of regex * regex * regex
| Swap of regex
| Swapinv of regex
| Proj of regex
| Projinv of regex
| AbortR of regex
| AbortRinv of regex
| AbortL of regex
| AbortLinv of regex
| DistL of regex * regex * regex
| DistLinv of regex * regex * regex
| DistR of regex * regex * regex
| DistRinv of regex * regex * regex
| Wrap of regex
| Wrapinv of regex
| Drop of regex * regex * dsl
| Cid of regex
| Ctrans of regex * regex * regex * dsl * dsl
| Cplus of regex * regex * regex * regex * dsl * dsl
| Cseq of regex * regex * regex * regex * dsl * dsl
| Dsl_var of Equality.sort * Equality.sort * Equality.sort
| Dsl_fix of regex * regex * dsl

(** val dropinv :
    Finite.coq_type -> (regex * regex) list -> regex -> regex
    -> dsl -> dsl **)

let dropinv _ _ a0 b0 x =
  Ctrans ((Plus (Eps, (Seq (b0, (Star a0))))), (Plus (Eps,
    (Seq (a0, (Star a0))))), (Star a0), (Cplus (Eps, Eps,
    (Seq (b0, (Star a0))), (Seq (a0, (Star a0))), (Cid Eps),
    (Cseq (b0, a0, (Star a0), (Star a0), (Ctrans (b0, (Plus
    (b0, Eps)), a0, (TagL (b0, Eps)), (Ctrans ((Plus (b0,
    Eps)), (Plus (Eps, b0)), a0, (Retag (b0, Eps)), x)))),
    (Cid (Star a0)))))), (Wrap a0))

(** val interp :
    Finite.coq_type -> (regex * regex) list -> regex -> regex
    -> dsl -> pTree -> (Equality.sort -> Equality.sort -> __
    -> pTree -> __ -> post) -> post **)

let rec interp af l _ _ p t f =
  match p with
  | Shuffle (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus ((Plus (a0, b0)), c)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Plus (a0, b0)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 _ -> P_inl (a0,
        (Plus (b0, c)), p1)) (fun _ _ _ p1 _ -> P_inr (a0,
        (Plus (b0, c)), (P_inl (b0, c, p1))))
        (fun _ _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ p0 _ -> P_inr (a0, (Plus (b0, c)), (P_inr
      (b0, c, p0)))) (fun _ _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ -> assert false
      (* absurd case *)) t f
  | Shuffleinv (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus (a0, (Plus (b0, c)))) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 _ -> P_inl ((Plus (a0,
      b0)), c, (P_inl (a0, b0, p0)))) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Plus (b0, c)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 _ -> P_inl ((Plus
        (a0, b0)), c, (P_inr (a0, b0, p1))))
        (fun _ _ _ p1 _ -> P_inr ((Plus (a0, b0)), c, p1))
        (fun _ _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | Retag (a0, b0) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus (a0, b0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 _ -> P_inr (b0, a0,
      p0)) (fun _ _ _ p0 _ -> P_inl (b0, a0, p0))
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | UntagL a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus (Empt, a0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Empt (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) p0 f0) (fun _ _ _ p0 _ -> p0)
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | UntagLinv a0 -> P_inr (Empt, a0, t)
  | Untag a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus (a0, a0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 _ -> p0)
      (fun _ _ _ p0 _ -> p0) (fun _ _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ -> assert false
      (* absurd case *)) t f
  | TagL (a0, b0) -> P_inl (a0, b0, t)
  | Assoc (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq ((Seq (a0, b0)), c)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (a0, b0)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p2 p3 _ -> P_pair (a0,
        (Seq (b0, c)), p2, (P_pair (b0, c, p3, p1))))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | Associnv (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (a0, (Seq (b0, c)))) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (b0, c)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p2 p3 _ -> P_pair ((Seq
        (a0, b0)), c, (P_pair (a0, b0, p0, p2)), p3))
        (fun _ _ _ _ -> assert false (* absurd case *)) p1 f0)
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | Swap a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (a0, Eps)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Eps (fun _ _ -> P_pair (Eps, a0, P_tt, p0))
        (fun _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ -> assert false (* absurd case *)) p1 f0)
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | Swapinv a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (Eps, a0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Eps (fun _ _ -> P_pair (a0, Eps, p1, P_tt))
        (fun _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ _ _ -> assert false (* absurd case *))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | Proj a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (Eps, a0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Eps (fun _ _ -> p1) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) p0 f0) (fun _ _ _ _ ->
      assert false (* absurd case *)) t f
  | Projinv a0 -> P_pair (Eps, a0, P_tt, t)
  | AbortR a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (a0, Empt)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Empt (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) p1 f0) (fun _ _ _ _ ->
      assert false (* absurd case *)) t f
  | AbortL a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (Empt, a0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 _ f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Empt (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) p0 f0) (fun _ _ _ _ ->
      assert false (* absurd case *)) t f
  | DistL (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (a0, (Plus (b0, c)))) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Plus (b0, c)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p2 _ -> P_inl ((Seq
        (a0, b0)), (Seq (a0, c)), (P_pair (a0, b0, p0, p2))))
        (fun _ _ _ p2 _ -> P_inr ((Seq (a0, b0)), (Seq (a0,
        c)), (P_pair (a0, c, p0, p2)))) (fun _ _ _ _ _ _ ->
        assert false (* absurd case *)) (fun _ _ _ _ ->
        assert false (* absurd case *)) p1 f0)
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | DistLinv (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus ((Seq (a0, b0)), (Seq (a0, c)))) (fun _ _ ->
      assert false (* absurd case *)) (fun _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (a0, b0)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 p2 _ -> P_pair (a0,
        (Plus (b0, c)), p1, (P_inl (b0, c, p2))))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (a0, c)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 p2 _ -> P_pair (a0,
        (Plus (b0, c)), p1, (P_inr (b0, c, p2))))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | DistR (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq ((Plus (a0, b0)), c)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Plus (a0, b0)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p2 _ -> P_inl ((Seq
        (a0, c)), (Seq (b0, c)), (P_pair (a0, c, p2, p1))))
        (fun _ _ _ p2 _ -> P_inr ((Seq (a0, c)), (Seq (b0,
        c)), (P_pair (b0, c, p2, p1)))) (fun _ _ _ _ _ _ ->
        assert false (* absurd case *)) (fun _ _ _ _ ->
        assert false (* absurd case *)) p0 f0)
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | DistRinv (a0, b0, c) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus ((Seq (a0, c)), (Seq (b0, c)))) (fun _ _ ->
      assert false (* absurd case *)) (fun _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (a0, c)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 p2 _ -> P_pair
        ((Plus (a0, b0)), c, (P_inl (a0, b0, p1)), p2))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (b0, c)) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 p2 _ -> P_pair
        ((Plus (a0, b0)), c, (P_inr (a0, b0, p1)), p2))
        (fun _ _ _ _ -> assert false (* absurd case *)) p0 f0)
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ -> assert false (* absurd case *)) t f
  | Wrap a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus (Eps, (Seq (a0, (Star a0))))) (fun _ _ ->
      assert false (* absurd case *)) (fun _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) Eps (fun _ _ -> P_fold (a0, (P_inl (Eps, (Seq
        (a0, (Star a0))), P_tt)))) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) p0 f0) (fun _ _ _ p0 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Seq (a0, (Star a0))) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ p1 p2 _ -> P_fold (a0,
        (P_inr (Eps, (Seq (a0, (Star a0))), (P_pair (a0,
        (Star a0), p1, p2)))))) (fun _ _ _ _ -> assert false
        (* absurd case *)) p0 f0) (fun _ _ _ _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ _ ->
      assert false (* absurd case *)) t f
  | Wrapinv a0 ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Star a0) (fun _ _ -> assert false (* absurd case *))
      (fun _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ p0 _ -> p0) t f
  | Drop (a0, b0, d) ->
    pTree_1size_rect
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Star a0) (fun u x f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Star a0) (fun _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ p0 x0 f1 ->
        pTree_case
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) (Plus (Eps, (Seq (a0, (Star a0)))))
          (fun _ _ _ -> assert false (* absurd case *))
          (fun _ _ _ _ -> assert false (* absurd case *))
          (fun _ _ _ p1 x1 f2 ->
          pTree_case
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) Eps (fun _ _ _ -> P_inl (Eps, (Seq (b0,
            (Star a0))), P_tt)) (fun _ _ _ _ -> assert false
            (* absurd case *)) (fun _ _ _ _ _ _ ->
            assert false (* absurd case *))
            (fun _ _ _ _ _ _ -> assert false
            (* absurd case *)) (fun _ _ _ _ _ _ _ ->
            assert false (* absurd case *)) (fun _ _ _ _ _ ->
            assert false (* absurd case *)) p1 x1 f2)
          (fun _ _ _ p1 x1 f2 ->
          pTree_case
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (Seq (a0, (Star a0))) (fun _ _ _ ->
            assert false (* absurd case *)) (fun _ _ _ _ ->
            assert false (* absurd case *))
            (fun _ _ _ _ _ _ -> assert false
            (* absurd case *)) (fun _ _ _ _ _ _ ->
            assert false (* absurd case *))
            (fun _ _ _ p2 p3 x2 f3 ->
            let hf = fun x3 y t0 -> f3 x3 y __ t0 __ in
            let __top_assumption_ =
              interp af l a0 (Plus (Eps, b0)) d p2
                (fun x3 y _ t0 _ -> hf x3 y t0)
            in
            pTree_case
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) (Plus (Eps, b0)) (fun _ _ _ ->
              assert false (* absurd case *)) (fun _ _ _ _ ->
              assert false (* absurd case *))
              (fun _ _ _ p4 _ _ ->
              pTree_case
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) Eps (fun _ _ _ ->
                let hf2 = fun x3 y t0 -> f3 x3 y __ t0 __ in
                let __top_assumption_0 =
                  x2 p3 __ (fun x3 y _ t0 _ -> hf2 x3 y t0)
                in
                pTree_case
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) (Plus (Eps, (Seq (b0, (Star a0)))))
                  (fun _ _ _ -> assert false
                  (* absurd case *)) (fun _ _ _ _ ->
                  assert false (* absurd case *))
                  (fun _ _ _ p5 _ _ ->
                  pTree_case
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) Eps (fun _ _ _ -> P_inl (Eps, (Seq
                    (b0, (Star a0))), P_tt)) (fun _ _ _ _ ->
                    assert false (* absurd case *))
                    (fun _ _ _ _ _ _ -> assert false
                    (* absurd case *)) (fun _ _ _ _ _ _ ->
                    assert false (* absurd case *))
                    (fun _ _ _ _ _ _ _ -> assert false
                    (* absurd case *)) (fun _ _ _ _ _ ->
                    assert false (* absurd case *)) p5 __ __)
                  (fun _ _ _ p5 _ _ -> P_inr (Eps, (Seq (b0,
                  (Star a0))), p5)) (fun _ _ _ _ _ _ _ ->
                  assert false (* absurd case *))
                  (fun _ _ _ _ _ -> assert false
                  (* absurd case *)) __top_assumption_0 __ __)
                (fun _ _ _ _ -> assert false
                (* absurd case *)) (fun _ _ _ _ _ _ ->
                assert false (* absurd case *))
                (fun _ _ _ _ _ _ -> assert false
                (* absurd case *)) (fun _ _ _ _ _ _ _ ->
                assert false (* absurd case *))
                (fun _ _ _ _ _ -> assert false
                (* absurd case *)) p4 __ __)
              (fun _ _ _ p4 _ _ -> P_inr (Eps, (Seq (b0,
              (Star a0))), (P_pair (b0, (Star a0), p4, p3))))
              (fun _ _ _ _ _ _ _ -> assert false
              (* absurd case *)) (fun _ _ _ _ _ ->
              assert false (* absurd case *))
              __top_assumption_ __ __) (fun _ _ _ _ _ ->
            assert false (* absurd case *)) p1 x1 f2)
          (fun _ _ _ _ _ _ _ -> assert false
          (* absurd case *)) (fun _ _ _ _ _ -> assert false
          (* absurd case *)) p0 x0 f1) u x f0) t f
  | Cid _ -> t
  | Ctrans (a0, b0, c, d, d0) ->
    let t' = interp af l a0 b0 d t f in
    let hf = fun x y t0 -> f x y __ t0 __ in
    interp af l b0 c d0 t' (fun x y _ t0 _ -> hf x y t0)
  | Cplus (a0, a', b0, b', d, d0) ->
    let h0 = interp af l a0 a' d in
    let h1 = interp af l b0 b' d0 in
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Plus (a0, b0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 f0 ->
      let hf0 = fun x y t0 -> f0 x y __ t0 __ in
      let t0 = h0 p0 (fun x y _ t0 _ -> hf0 x y t0) in
      P_inl (a', b', t0)) (fun _ _ _ p0 f0 ->
      let hf = fun x y t0 -> f0 x y __ t0 __ in
      let t1 = h1 p0 (fun x y _ t0 _ -> hf x y t0) in
      P_inr (a', b', t1)) (fun _ _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ -> assert false
      (* absurd case *)) t f
  | Cseq (a0, a', b0, b', d, d0) ->
    let h0 = interp af l a0 a' d in
    let h1 = interp af l b0 b' d0 in
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq (a0, b0)) (fun _ _ -> assert false
      (* absurd case *)) (fun _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ _ _ -> assert false
      (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      let hf0 = fun x y t0 -> f0 x y __ t0 __ in
      let hf1 = fun x y t0 -> f0 x y __ t0 __ in
      let t0' = h0 p0 (fun x y _ t0 _ -> hf0 x y t0) in
      let t1' = h1 p1 (fun x y _ t0 _ -> hf1 x y t0) in
      P_pair (a', b', t0', t1')) (fun _ _ _ _ -> assert false
      (* absurd case *)) t f
  | Dsl_var (a0, a1, b0) ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Seq ((Event a0), (Obj.magic a1))) (fun _ _ ->
      assert false (* absurd case *)) (fun _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ _ _ ->
      assert false (* absurd case *)) (fun _ _ _ p0 p1 f0 ->
      pTree_case
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) (Event a0) (fun _ _ -> assert false
        (* absurd case *)) (fun _ _ f1 ->
        let __top_assumption_ = f1 a1 b0 __ p1 __ in
        P_pair ((Event a0), (Obj.magic b0), (P_singl a0),
        __top_assumption_)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ _ _ -> assert false
        (* absurd case *)) (fun _ _ _ _ -> assert false
        (* absurd case *)) p0 f0) (fun _ _ _ _ ->
      assert false (* absurd case *)) t f
  | Dsl_fix (r0, r1, p0) ->
    pTree_0size_rect
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      r0 (fun hin iH hf ->
      Obj.magic interp af ((r0, r1) :: l) r0 r1 p0 hin
        (fun x y _ t0 _ ->
        let b0 =
          eq_op0
            (datatypes_prod__canonical__eqtype_Equality
              (regex_regex__canonical__eqtype_Equality
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af))
              (regex_regex__canonical__eqtype_Equality
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af))) (Obj.magic (x, y))
            (Obj.magic (r0, r1))
        in
        if b0
        then iH t0 __ (fun x' y' _ t1 _ -> hf x' y' __ t1 __)
        else Obj.magic hf x y __ t0 __)) t f
  | _ ->
    pTree_case
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      Empt (fun _ _ -> assert false (* absurd case *))
      (fun _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ _ _ -> assert false (* absurd case *))
      (fun _ _ _ _ -> assert false (* absurd case *)) t f

(** val o_plus_l :
    Finite.coq_type -> regex -> regex -> (regex * regex) list
    -> dsl **)

let o_plus_l af c0 c1 _ =
  let b0 =
    nu
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      c0
  in
  if b0
  then let b1 =
         nu
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) c1
       in
       if b1 then TagL (Eps, Eps) else TagL (Eps, Empt)
  else let b1 =
         nu
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) c1
       in
       if b1 then UntagLinv Eps else TagL (Empt, Empt)

(** val o_plus_r :
    Finite.coq_type -> regex -> regex -> (regex * regex) list
    -> dsl **)

let o_plus_r af c0 c1 _ =
  let b0 =
    nu
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      c0
  in
  if b0
  then let b1 =
         nu
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) c1
       in
       if b1
       then Untag Eps
       else Dsl_fix ((Plus (Eps, Empt)), Eps, (Dsl_fix ((Plus
              (Eps, Empt)), Eps, (Dsl_fix ((Plus (Eps,
              Empt)), Eps, (Ctrans ((Plus (Eps, Empt)), (Plus
              (Empt, Eps)), Eps, (Retag (Eps, Empt)), (UntagL
              Eps))))))))
  else let b1 =
         nu
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) c1
       in
       if b1 then UntagL Eps else Untag Empt

(** val ctrans1 :
    Finite.coq_type -> regex -> (regex * regex) list -> regex
    -> regex -> dsl -> dsl -> dsl **)

let ctrans1 _ c0 _ c1 c2 x x0 =
  Ctrans (c0, c1, c2, x, x0)

(** val ctrans2 :
    Finite.coq_type -> regex -> (regex * regex) list -> regex
    -> regex -> dsl -> dsl -> dsl **)

let ctrans2 _ c0 _ c1 c2 x x0 =
  Ctrans (c0, c1, c2, x0, x)

(** val cplus1 :
    Finite.coq_type -> regex -> regex -> (regex * regex) list
    -> regex -> regex -> dsl -> dsl -> dsl **)

let cplus1 _ c0 c0' _ c1 c1' x x0 =
  Cplus (c0, c0', c1, c1', x, x0)

(** val cplus2 :
    Finite.coq_type -> regex -> regex -> (regex * regex) list
    -> regex -> regex -> dsl -> dsl -> dsl **)

let cplus2 _ c0 c0' _ c1 c1' x x0 =
  Cplus (c0, c0', c1, c1', x0, x)

(** val cseq1 :
    Finite.coq_type -> regex -> regex -> regex -> regex ->
    (regex * regex) list -> dsl -> dsl -> dsl **)

let cseq1 _ c0 c0' c1 c1' _ x x0 =
  Cseq (c0, c0', c1, c1', x, x0)

(** val split_plus_l :
    Finite.coq_type -> (regex * regex) list ->
    Equality.coq_type -> Equality.sort list -> (Equality.sort
    -> regex) -> (Equality.sort -> regex) -> dsl **)

let split_plus_l af r _ _l_ p p' =
  let _evar_0_ = TagL (Empt, Empt) in
  let _evar_0_0 = fun a0 l iH ->
    ctrans1 af (Plus ((Plus ((p a0), (p' a0))),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
        (p' j)))))))) r (Plus ((p a0), (Plus ((p' a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
        (p' j)))))))))) (Plus ((Plus ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))))), (Plus
      ((p' a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
      (Shuffle ((p a0), (p' a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
        (p' j))))))))
      (ctrans2 af (Plus ((p a0), (Plus ((p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
          (p' j)))))))))) r (Plus ((p a0), (Plus
        ((Coq_bigop.body Empt l (fun j -> BigBody (j,
           (fun x x0 -> Plus (x, x0)), true, (p j)))), (Plus
        ((p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (p' j))))))))))
        (Plus ((Plus ((p a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (p j)))))), (Plus
        ((p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
        (Shuffleinv ((p a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (p j)))), (Plus
        ((p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
        (cplus1 af (p a0) (p a0) r (Plus ((p' a0),
          (Coq_bigop.body Empt l (fun j -> BigBody (j,
            (fun x x0 -> Plus (x, x0)), true, (Plus (
            (p j), (p' j)))))))) (Plus
          ((Coq_bigop.body Empt l (fun j -> BigBody (j,
             (fun x x0 -> Plus (x, x0)), true, (p j)))),
          (Plus ((p' a0),
          (Coq_bigop.body Empt l (fun j -> BigBody (j,
            (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
          (Cid (p a0))
          (ctrans2 af (Plus ((p' a0),
            (Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (Plus (
              (p j), (p' j)))))))) r (Plus ((p' a0), (Plus
            ((Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (p' j)))),
            (Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (p j))))))))
            (Plus
            ((Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (p j)))),
            (Plus ((p' a0),
            (Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
            (ctrans2 af (Plus ((p' a0), (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))))
              r (Plus ((Plus ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))
              (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p j)))),
              (Plus ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
              (Retag ((Plus ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))
              (Shuffleinv ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))))
            (cplus1 af (p' a0) (p' a0) r
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Plus
                ((p j), (p' j)))))) (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))
              (Cid (p' a0)) (Ctrans
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (Plus
                 ((p j), (p' j)))))), (Plus
              ((Coq_bigop.body Empt l (fun a1 -> BigBody (a1,
                 (fun x x0 -> Plus (x, x0)), true, (p a1)))),
              (Coq_bigop.body Empt l (fun a1 -> BigBody (a1,
                (fun x x0 -> Plus (x, x0)), true, (p' a1)))))),
              (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              iH, (Retag
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j))))))))))))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _l_

(** val split_plus_r :
    Finite.coq_type -> (regex * regex) list ->
    Equality.coq_type -> Equality.sort list -> (Equality.sort
    -> regex) -> (Equality.sort -> regex) -> dsl **)

let split_plus_r af r _ _l_ p p' =
  let _evar_0_ = Untag Empt in
  let _evar_0_0 = fun a0 l iH ->
    ctrans1 af (Plus ((Plus ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))))), (Plus
      ((p' a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p' j)))))))) r
      (Plus ((p a0), (Plus
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x x0 -> Plus (x, x0)), true, (p j)))), (Plus
      ((p' a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p' j))))))))))
      (Plus ((Plus ((p a0), (p' a0))),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
        (p' j)))))))) (Shuffle ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))), (Plus
      ((p' a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
      (ctrans2 af (Plus ((p a0), (Plus
        ((Coq_bigop.body Empt l (fun j -> BigBody (j,
           (fun x x0 -> Plus (x, x0)), true, (p j)))), (Plus
        ((p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (p' j)))))))))) r
        (Plus ((p a0), (Plus ((p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
          (p' j)))))))))) (Plus ((Plus ((p a0), (p' a0))),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
          (p' j)))))))) (Shuffleinv ((p a0), (p' a0),
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (Plus ((p j),
          (p' j))))))))
        (cplus1 af (p a0) (p a0) r (Plus
          ((Coq_bigop.body Empt l (fun j -> BigBody (j,
             (fun x x0 -> Plus (x, x0)), true, (p j)))),
          (Plus ((p' a0),
          (Coq_bigop.body Empt l (fun j -> BigBody (j,
            (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
          (Plus ((p' a0),
          (Coq_bigop.body Empt l (fun j -> BigBody (j,
            (fun x x0 -> Plus (x, x0)), true, (Plus (
            (p j), (p' j)))))))) (Cid (p a0))
          (ctrans1 af (Plus
            ((Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (p j)))),
            (Plus ((p' a0),
            (Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
            r (Plus ((p' a0), (Plus
            ((Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (p' j)))),
            (Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (p j))))))))
            (Plus ((p' a0),
            (Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (Plus (
              (p j), (p' j))))))))
            (ctrans1 af (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p j)))),
              (Plus ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
              r (Plus ((Plus ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))
              (Plus ((p' a0), (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))))
              (Retag
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p j)))),
              (Plus ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j))))))))
              (Shuffle ((p' a0),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))))
            (cplus1 af (p' a0) (p' a0) r (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Plus
                ((p j), (p' j)))))) (Cid (p' a0)) (Ctrans
              ((Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Plus
                ((p j), (p' j)))))), (Cid (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))),
              (Ctrans ((Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Plus
                ((p j), (p' j)))))), (Cid (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))),
              (Ctrans ((Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Plus
                ((p j), (p' j)))))), (Cid (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j))))))),
              (Ctrans ((Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              (Plus
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p' j)))))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Plus
                ((p j), (p' j)))))), (Retag
              ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (p' j)))),
              (Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (p j)))))),
              iH))))))))))))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _l_

(** val factor_seq_r_l :
    Finite.coq_type -> (regex * regex) list ->
    Equality.coq_type -> Equality.sort list -> (Equality.sort
    -> regex) -> regex -> dsl **)

let factor_seq_r_l af r _ _l_ p c =
  let _evar_0_ = AbortLinv c in
  let _evar_0_0 = fun a0 l iH ->
    ctrans2 af (Plus ((Seq ((p a0), c)),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Seq ((p j), c)))))))
      r (Plus ((Seq ((p a0), c)), (Seq
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x x0 -> Plus (x, x0)), true, (p j)))), c))))
      (Seq ((Plus ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))))), c))
      (DistRinv ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))), c))
      (Cplus ((Seq ((p a0), c)), (Seq ((p a0), c)),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Seq ((p j), c))))),
      (Seq
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x x0 -> Plus (x, x0)), true, (p j)))), c)),
      (Cid (Seq ((p a0), c))), iH))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _l_

(** val factor_seq_r_r :
    Finite.coq_type -> (regex * regex) list ->
    Equality.coq_type -> Equality.sort list -> (Equality.sort
    -> regex) -> regex -> dsl **)

let factor_seq_r_r af r _ _l_ p c =
  let _evar_0_ = AbortL c in
  let _evar_0_0 = fun a0 l iH ->
    ctrans1 af (Seq ((Plus ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))))), c)) r
      (Plus ((Seq ((p a0), c)), (Seq
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x x0 -> Plus (x, x0)), true, (p j)))), c))))
      (Plus ((Seq ((p a0), c)),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Seq ((p j), c)))))))
      (DistR ((p a0),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (p j)))), c))
      (Cplus ((Seq ((p a0), c)), (Seq ((p a0), c)), (Seq
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x x0 -> Plus (x, x0)), true, (p j)))), c)),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Seq ((p j), c))))),
      (Cid (Seq ((p a0), c))), iH))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _l_

(** val eps_c_l :
    Finite.coq_type -> regex -> (regex * regex) list -> dsl **)

let eps_c_l af r r0 =
  Ctrans ((Seq (r, Eps)), (Seq (Eps, r)), r,
    (ctrans1 af (Seq (r, Eps)) r0 (Seq (Eps, r)) (Seq (Eps,
      r)) (Swap r) (Cid (Seq (Eps, r)))), (Proj r))

type 'r ex_coerce = Equality.sort -> __ -> 'r

(** val eq_big_plus_c :
    Finite.coq_type -> Finite.sort list -> (Finite.sort ->
    regex) -> (Finite.sort -> regex) -> (regex * regex) list
    -> dsl ex_coerce -> dsl **)

let eq_big_plus_c af _l_ f1 f2 r =
  let _evar_0_ = fun _ -> Cid Empt in
  let _evar_0_0 = fun a0 l iH hin ->
    cplus1 af (f1 a0) (f2 a0) r
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (f1 j))))
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (f2 j))))
      (hin a0 __) (iH (fun a1 _ -> hin a1 __))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _l_

(** val plus_empt_l :
    Finite.coq_type -> Equality.coq_type -> (regex * regex)
    list -> Equality.sort list -> dsl **)

let plus_empt_l af _ r _top_assumption_ =
  let _evar_0_ = Cid Empt in
  let _evar_0_0 = fun _ l iH ->
    ctrans2 af (Plus (Empt,
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, Empt))))) r (Plus
      (Empt, Empt)) Empt (Untag Empt)
      (cplus1 af Empt Empt r
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, Empt))) Empt (Cid
        Empt) iH)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _top_assumption_

(** val big_event_notin_l :
    Finite.coq_type -> (regex * regex) list -> Equality.sort
    pred_sort -> Equality.sort -> dsl **)

let big_event_notin_l af r _top_assumption_ a0 =
  let _evar_0_ = fun _ -> Cid Empt in
  let _evar_0_0 = fun a1 l iH a2 ->
    let iH0 = iH a2 __ in
    ctrans2 af (Plus ((Seq ((Event a1), Empt)),
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x x0 -> Plus (x, x0)), true, (Seq ((Event j),
        (if eq_op0
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a2 j
         then Eps
         else Empt)))))))) r (Plus (Empt, Empt)) Empt (Untag
      Empt)
      (cplus1 af (Seq ((Event a1), Empt)) Empt r
        (Coq_bigop.body Empt l (fun j -> BigBody (j,
          (fun x x0 -> Plus (x, x0)), true, (Seq ((Event j),
          (if eq_op0
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a2 j
           then Eps
           else Empt)))))) Empt (AbortR (Event a1)) iH0)
  in
  let rec f l a1 =
    match l with
    | [] -> _evar_0_ a1
    | y :: l0 -> _evar_0_0 y l0 (fun a2 _ -> f l0 a2) a1
  in f (Obj.magic _top_assumption_) a0

(** val big_event_in_l :
    Finite.coq_type -> (regex * regex) list -> Equality.sort
    pred_sort -> Equality.sort -> dsl **)

let big_event_in_l af r _top_assumption_ a0 =
  let _evar_0_ = fun _ -> assert false (* absurd case *) in
  let _evar_0_0 = fun a1 l iH a2 ->
    let b0 =
      eq_op0
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a2 a1
    in
    (fun _ ->
    if b0
    then let _evar_0_0 = fun _ ->
           let iH0 = iH a1 __ in
           ctrans2 af (Plus ((Seq ((Event a1), Eps)),
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a1 j
                then Eps
                else Empt)))))))) r (Plus ((Event a1), (Event
             a1))) (Event a1) (Untag (Event a1))
             (cplus1 af (Seq ((Event a1), Eps)) (Event a1) r
               (Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (Seq
                 ((Event j),
                 (if eq_op0
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a1 j
                  then Eps
                  else Empt)))))) (Event a1)
               (eps_c_l af (Event a1) r) iH0)
         in
         let _evar_0_1 = fun _ ->
           ctrans1 af (Plus ((Seq ((Event a1), Eps)),
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a1 j
                then Eps
                else Empt)))))))) r (Plus ((Event a1), Empt))
             (Event a1)
             (cplus1 af (Seq ((Event a1), Eps)) (Event a1) r
               (Coq_bigop.body Empt l (fun j -> BigBody (j,
                 (fun x x0 -> Plus (x, x0)), true, (Seq
                 ((Event j),
                 (if eq_op0
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a1 j
                  then Eps
                  else Empt)))))) Empt
               (eps_c_l af (Event a1) r)
               (big_event_notin_l af r (Obj.magic l) a1))
             (Dsl_fix ((Plus ((Event a1), Empt)), (Event a1),
             (Dsl_fix ((Plus ((Event a1), Empt)), (Event a1),
             (Dsl_fix ((Plus ((Event a1), Empt)), (Event a1),
             (Ctrans ((Plus ((Event a1), Empt)), (Plus (Empt,
             (Event a1))), (Event a1), (Retag ((Event a1),
             Empt)), (UntagL (Event a1))))))))))
         in
         if in_mem a1
              (mem
                (seq_predType
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af)) (Obj.magic l))
         then _evar_0_0 __
         else _evar_0_1 __
    else let iH0 = iH a2 __ in
         ctrans1 af (Plus ((Seq ((Event a1), Empt)),
           (Coq_bigop.body Empt l (fun j -> BigBody (j,
             (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
             j),
             (if eq_op0
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a2 j
              then Eps
              else Empt)))))))) r (Plus ((Seq ((Event a1),
           Empt)), (Event a2))) (Event a2)
           (cplus1 af (Seq ((Event a1), Empt)) (Seq ((Event
             a1), Empt)) r
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a2 j
                then Eps
                else Empt)))))) (Event a2) (Cid (Seq ((Event
             a1), Empt))) iH0) (Dsl_fix ((Plus ((Seq ((Event
           a1), Empt)), (Event a2))), (Event a2), (Dsl_fix
           ((Plus ((Seq ((Event a1), Empt)), (Event a2))),
           (Event a2), (Ctrans ((Plus ((Seq ((Event a1),
           Empt)), (Event a2))), (Plus (Empt, (Event a2))),
           (Event a2), (Cplus ((Seq ((Event a1), Empt)),
           Empt, (Event a2), (Event a2), (AbortR (Event a1)),
           (Cid (Event a2)))), (UntagL (Event a2)))))))))
  in
  let rec f = function
  | [] -> (fun a1 _ -> _evar_0_ a1)
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f (Obj.magic _top_assumption_) a0 __

(** val big_event_in_r :
    Finite.coq_type -> (regex * regex) list -> Equality.sort
    pred_sort -> Equality.sort -> dsl **)

let big_event_in_r af r _top_assumption_ a0 =
  let _evar_0_ = fun _ -> assert false (* absurd case *) in
  let _evar_0_0 = fun a1 l iH a2 ->
    let b0 =
      eq_op0
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a2 a1
    in
    (fun _ ->
    if b0
    then let _evar_0_0 = fun _ ->
           ctrans2 af (Event a1) r (Seq ((Event a1), Eps))
             (Plus ((Seq ((Event a1), Eps)),
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a1 j
                then Eps
                else Empt)))))))) (TagL ((Seq ((Event a1),
             Eps)),
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a1 j
                then Eps
                else Empt)))))))) (Dsl_fix ((Event a1), (Seq
             ((Event a1), Eps)), (Dsl_fix ((Event a1), (Seq
             ((Event a1), Eps)), (Dsl_fix ((Event a1), (Seq
             ((Event a1), Eps)), (Ctrans ((Event a1), (Seq
             (Eps, (Event a1))), (Seq ((Event a1), Eps)),
             (Projinv (Event a1)), (Swapinv (Event
             a1))))))))))
         in
         let _evar_0_1 = fun _ ->
           ctrans2 af (Event a1) r (Seq ((Event a1), Eps))
             (Plus ((Seq ((Event a1), Eps)),
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a1 j
                then Eps
                else Empt)))))))) (TagL ((Seq ((Event a1),
             Eps)),
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a1 j
                then Eps
                else Empt)))))))) (Dsl_fix ((Event a1), (Seq
             ((Event a1), Eps)), (Dsl_fix ((Event a1), (Seq
             ((Event a1), Eps)), (Dsl_fix ((Event a1), (Seq
             ((Event a1), Eps)), (Ctrans ((Event a1), (Seq
             (Eps, (Event a1))), (Seq ((Event a1), Eps)),
             (Projinv (Event a1)), (Swapinv (Event
             a1))))))))))
         in
         if in_mem a1
              (mem
                (seq_predType
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af)) (Obj.magic l))
         then _evar_0_0 __
         else _evar_0_1 __
    else let iH0 = iH a2 __ in
         ctrans2 af (Event a2) r (Plus
           ((Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
              j),
              (if eq_op0
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a2 j
               then Eps
               else Empt)))))), (Seq ((Event a1), Empt))))
           (Plus ((Seq ((Event a1), Empt)),
           (Coq_bigop.body Empt l (fun j -> BigBody (j,
             (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
             j),
             (if eq_op0
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a2 j
              then Eps
              else Empt)))))))) (Retag
           ((Coq_bigop.body Empt l (fun j -> BigBody (j,
              (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
              j),
              (if eq_op0
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a2 j
               then Eps
               else Empt)))))), (Seq ((Event a1), Empt))))
           (ctrans2 af (Event a2) r
             (Coq_bigop.body Empt l (fun j -> BigBody (j,
               (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
               j),
               (if eq_op0
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a2 j
                then Eps
                else Empt)))))) (Plus
             ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Seq
                ((Event j),
                (if eq_op0
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a2 j
                 then Eps
                 else Empt)))))), (Seq ((Event a1), Empt))))
             (TagL
             ((Coq_bigop.body Empt l (fun j -> BigBody (j,
                (fun x x0 -> Plus (x, x0)), true, (Seq
                ((Event j),
                (if eq_op0
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a2 j
                 then Eps
                 else Empt)))))), (Seq ((Event a1), Empt))))
             iH0))
  in
  let rec f = function
  | [] -> (fun a1 _ -> _evar_0_ a1)
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f (Obj.magic _top_assumption_) a0 __

(** val derive_unfold_coerce :
    Finite.coq_type -> regex -> dsl **)

let derive_unfold_coerce af __top_assumption_ =
  let _evar_0_ = TagL
    ((o
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       Eps),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 Eps)))))))
  in
  let _evar_0_0 = TagL
    ((o
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       Empt),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 Empt)))))))
  in
  let _evar_0_1 = fun s -> Dsl_fix ((Event s), (Plus
    ((o
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       (Event s)),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 (Event s))))))))),
    (ctrans2 af (Event s) (((Event s), (Plus (Empt,
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (if eq_op0
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) s a0
         then Eps
         else Empt))))))))) :: []) (Plus
      ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
         BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
         ((Event a0),
         (if eq_op0
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) s a0
          then Eps
          else Empt)))))), Empt)) (Plus (Empt,
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (if eq_op0
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) s a0
         then Eps
         else Empt)))))))) (Retag
      ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
         BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
         ((Event a0),
         (if eq_op0
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) s a0
          then Eps
          else Empt)))))), Empt))
      (ctrans2 af (Event s) (((Event s), (Plus (Empt,
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (if eq_op0
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) s a0
           then Eps
           else Empt))))))))) :: [])
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (if eq_op0
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) s a0
           then Eps
           else Empt)))))) (Plus
        ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (if eq_op0
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) s a0
            then Eps
            else Empt)))))), Empt)) (TagL
        ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (if eq_op0
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) s a0
            then Eps
            else Empt)))))), Empt))
        (big_event_in_r af (((Event s), (Plus (Empt,
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (if eq_op0
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) s a0
             then Eps
             else Empt))))))))) :: [])
          (Obj.magic index_enum af) s))))
  in
  let _evar_0_2 = fun r0 hd0 r1 hd1 ->
    ctrans1 af (Plus (r0, r1)) [] (Plus ((Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) r0),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0)))))))), (Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) r1),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r1)))))))))) (Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) (Plus (r0, r1))),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 (Plus (r0, r1))))))))))
      (cplus1 af r0 (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)))))))) [] r1 (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1)))))))) hd0 hd1)
      (ctrans1 af (Plus ((Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)))))))), (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1)))))))))) [] (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0), (Plus
        ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0)))))), (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1)))))))))))) (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) (Plus (r0, r1))),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 (Plus (r0, r1)))))))))) (Shuffle
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)))))), (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1))))))))))
        (ctrans2 af (Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) r0), (Plus
          ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0)))))), (Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) r1),
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r1)))))))))))) [] (Plus ((Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) r0),
          (o
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) r1))),
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 (Plus (r0, r1)))))))))) (Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) (Plus (r0, r1))),
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 (Plus (r0, r1))))))))))
          (cplus1 af (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0),
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1)))
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) (Plus (r0, r1))) []
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))
            (o_plus_r af r0 r1 []) (Cid
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))))
          (ctrans2 af (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0), (Plus
            ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0)))))), (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r1)))))))))))) [] (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0), (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1)))))))))))) (Plus
            ((Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0),
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1))),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1)))))))))) (Shuffleinv
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0),
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))))
            (cplus1 af
              (o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r0)
              (o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r0) [] (Plus
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Plus
              ((o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1),
              (Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r1)))))))))) (Plus
              ((o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1),
              (Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 (Plus (r0, r1)))))))))) (Cid
              (o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r0))
              (ctrans1 af (Plus
                ((Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), (Plus
                ((o
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) r1),
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r1)))))))))) [] (Plus
                ((o
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) r1), (Plus
                ((Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1)))))),
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))))))) (Plus
                ((o
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) r1),
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 (Plus (r0, r1))))))))))
                (ctrans1 af (Plus
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0)))))), (Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))))))) [] (Plus ((Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))) (Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1), (Plus
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))))) (Retag
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0)))))), (Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))))))) (Shuffle
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))))
                (cplus1 af
                  (o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1)
                  (o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1) [] (Plus
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0))))))))
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 (Plus (r0, r1)))))))) (Cid
                  (o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1))
                  (ctrans2 af (Plus
                    ((Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))),
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))))) []
                    (Coq_bigop.body Empt (index_enum af)
                      (fun i -> BigBody (i, (fun x x0 -> Plus
                      (x, x0)), true, (Plus ((Seq ((Event i),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) i r0))), (Seq ((Event i),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) i r1))))))))
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (Plus
                      ((derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r1))))))))
                    (eq_big_plus_c af (index_enum af)
                      (fun a0 -> Plus ((Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0))), (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r1))))) (fun i -> Seq
                      ((Event i), (Plus
                      ((derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) i r0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) i r1))))) [] (fun a0 _ ->
                      DistLinv ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r1))))
                    (ctrans2 af (Plus
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))),
                      (Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))))) [] (Plus
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))),
                      (Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0))))))))
                      (Coq_bigop.body Empt (index_enum af)
                        (fun i -> BigBody (i, (fun x x0 ->
                        Plus (x, x0)), true, (Plus ((Seq
                        ((Event i),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) i r0))), (Seq ((Event i),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) i r1))))))))
                      (ctrans2 af (Plus
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))),
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))))) [] (Plus
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))),
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1))))))))
                        (Coq_bigop.body Empt (index_enum af)
                          (fun i -> BigBody (i, (fun x x0 ->
                          Plus (x, x0)), true, (Plus ((Seq
                          ((Event i),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) i r0))), (Seq ((Event i),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) i r1))))))))
                        (split_plus_r af []
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) (index_enum af) (fun a0 ->
                          Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))) (fun a0 -> Seq
                          ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))) (Retag
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))),
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))))))
                      (cplus1 af
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1))))))
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))))) []
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))))))
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))) (Cid
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1))))))) (Cid
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))))))))))))))))
  in
  let _evar_0_3 = fun r0 hd0 r1 hd1 ->
    let b0 =
      nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) r0
    in
    if b0
    then ctrans2 af (Seq (r0, r1)) [] (Plus
           ((o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1),
           (Coq_bigop.body Empt (index_enum af) (fun i ->
             BigBody (i, (fun x x0 -> Plus (x, x0)), true,
             (Plus ((Seq ((Seq ((Event i),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r0))), r1)), (Seq ((Event i),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r1)))))))))) (Plus
           ((o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1),
           (Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0), (Plus ((Seq
             ((derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r0), r1)),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r1))))))))))
           (cplus2 af
             (o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1)
             (o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1) []
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Plus ((Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)), (Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r1))))))))
             (Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0), (Plus ((Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0), r1)),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r1))))))))
             (eq_big_plus_c af (index_enum af) (fun a0 ->
               Plus ((Seq ((Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0))), r1)), (Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r1))))) (fun i -> Seq ((Event i),
               (Plus ((Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) i r0), r1)),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r1))))) [] (fun a0 _ ->
               ctrans2 af (Plus ((Seq ((Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0))), r1)), (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))) [] (Plus ((Seq ((Event
                 a0), (Seq
                 ((derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0), r1)))), (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))) (Seq ((Event a0), (Plus
                 ((Seq
                 ((derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0), r1)),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))) (DistLinv ((Event a0),
                 (Seq
                 ((derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0), r1)),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1)))
                 (cplus1 af (Seq ((Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0))), r1)) (Seq ((Event a0),
                   (Seq
                   ((derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0), r1)))) [] (Seq ((Event
                   a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))) (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))) (Assoc ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0), r1)) (Cid (Seq ((Event
                   a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))))))) (Cid
             (o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1)))
           (ctrans2 af (Seq (r0, r1)) [] (Plus
             ((o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r1), (Plus ((Seq
             ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0)))))), r1)),
             (Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r1)))))))))) (Plus
             ((o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r1),
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Plus ((Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)), (Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r1))))))))))
             (cplus2 af
               (o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1)
               (o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1) [] (Plus ((Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1)),
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))))))
               (Coq_bigop.body Empt (index_enum af) (fun i ->
                 BigBody (i, (fun x x0 -> Plus (x, x0)),
                 true, (Plus ((Seq ((Seq ((Event i),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) i r0))), r1)), (Seq ((Event i),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) i r1))))))))
               (ctrans2 af (Plus ((Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)),
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1)))))))) [] (Plus
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0))), r1))))),
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))))))))
                 (Coq_bigop.body Empt (index_enum af)
                   (fun i -> BigBody (i, (fun x x0 -> Plus
                   (x, x0)), true, (Plus ((Seq ((Seq ((Event
                   i),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) i r0))), r1)), (Seq ((Event i),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) i r1))))))))
                 (split_plus_r af []
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) (index_enum af) (fun a0 -> Seq ((Seq
                   ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0))), r1)) (fun a0 -> Seq
                   ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))))
                 (cplus1 af (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1))
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Seq ((Event
                     a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0))), r1))))) []
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))
                   (factor_seq_r_r af []
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) (index_enum af) (fun a0 -> Seq
                     ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0))) r1) (Cid
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))))) (Cid
               (o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1)))
             (ctrans1 af (Seq (r0, r1)) [] (Seq ((Plus (Eps,
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))))), r1)) (Plus
               ((o
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) r1), (Plus ((Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1)),
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))))))))
               (cseq1 af r0 (Plus (Eps,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))) r1 r1 [] hd0 (Cid
                 r1))
               (ctrans1 af (Seq ((Plus (Eps,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))), r1)) [] (Plus ((Seq
                 (Eps, r1)), (Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)))) (Plus
                 ((o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1), (Plus ((Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)),
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1)))))))))) (DistR (Eps,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), r1))
                 (ctrans1 af (Plus ((Seq (Eps, r1)), (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) [] (Plus
                   ((Plus
                   ((o
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) r1),
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))))), (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) (Plus
                   ((o
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) r1), (Plus ((Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)),
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))))))
                   (cplus1 af (Seq (Eps, r1)) (Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))))) [] (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)) (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))
                     (ctrans1 af (Seq (Eps, r1)) [] r1 (Plus
                       ((o
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) r1),
                       (Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))))) (Proj r1) hd1)
                     (Cid (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))))
                   (ctrans1 af (Plus ((Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))))), (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)))) [] (Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1), (Plus
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r1)))))), (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)))))) (Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1), (Plus ((Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))))))) (Shuffle
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))), (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))))
                     (cplus1 af
                       (o
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) r1)
                       (o
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) r1) [] (Plus
                       ((Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))))), (Seq
                       ((Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))), r1)))) (Plus
                       ((Seq
                       ((Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))), r1)),
                       (Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))))) (Cid
                       (o
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) r1))
                       (ctrans1 af (Plus
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r1)))))), (Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)))) []
                         (Plus ((Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)),
                         (Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))))) (Plus ((Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)),
                         (Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))))) (Retag
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r1)))))), (Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)))) (Cid
                         (Plus ((Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)),
                         (Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1))))))))))))))))
    else ctrans2 af (Seq (r0, r1)) [] (Plus (Empt,
           (Coq_bigop.body Empt (index_enum af) (fun i ->
             BigBody (i, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Seq ((Event i),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r0))), r1))))))) (Plus (Empt,
           (Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0), (Seq
             ((derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r0), r1)))))))))
           (cplus2 af Empt Empt []
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)))))
             (Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0), (Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0), r1)))))))
             (eq_big_plus_c af (index_enum af) (fun a0 -> Seq
               ((Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0))), r1)) (fun i -> Seq ((Event
               i), (Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) i r0), r1)))) [] (fun a0 _ -> Assoc
               ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0), r1))) (Cid Empt))
           (ctrans2 af (Seq (r0, r1)) [] (Plus (Empt, (Seq
             ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0)))))), r1)))) (Plus (Empt,
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)))))))
             (cplus2 af Empt Empt [] (Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1))
               (Coq_bigop.body Empt (index_enum af) (fun i ->
                 BigBody (i, (fun x x0 -> Plus (x, x0)),
                 true, (Seq ((Seq ((Event i),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) i r0))), r1)))))
               (factor_seq_r_r af []
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) (index_enum af) (fun a0 -> Seq ((Event
                 a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0))) r1) (Cid Empt))
             (ctrans1 af (Seq (r0, r1)) [] (Seq ((Plus (Empt,
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))))), r1)) (Plus (Empt,
               (Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1))))
               (cseq1 af r0 (Plus (Empt,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))) r1 r1 [] hd0 (Cid
                 r1))
               (ctrans1 af (Seq ((Plus (Empt,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))), r1)) [] (Plus ((Seq
                 (Empt, r1)), (Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)))) (Plus (Empt,
                 (Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)))) (DistR (Empt,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), r1))
                 (ctrans1 af (Plus ((Seq (Empt, r1)), (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) [] (Plus
                   (Empt, (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) (Plus
                   (Empt, (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1))))
                   (cplus1 af (Seq (Empt, r1)) Empt [] (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)) (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)) (AbortL r1)
                     (Cid (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)))) (Cid
                   (Plus (Empt, (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))))))))
  in
  let _evar_0_4 = fun r0 hd0 ->
    ctrans2 af (Star r0) [] (Plus (Eps, (Seq
      ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
         BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
         ((Event a0),
         (derive
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r0)))))), (Star r0))))) (Plus (Eps,
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0), (Seq
        ((derive
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r0), (Star r0))))))))))
      (cplus2 af Eps Eps [] (Seq
        ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0)))))), (Star r0)))
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0), (Seq
          ((derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0), (Star r0))))))))
        (ctrans2 af (Seq
          ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0)))))), (Star r0))) []
          (Coq_bigop.body Empt (index_enum af) (fun i ->
            BigBody (i, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Seq ((Event i),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) i r0))), (Star r0))))))
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0), (Seq
            ((derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0), (Star r0))))))))
          (eq_big_plus_c af (index_enum af) (fun a0 -> Seq
            ((Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r0))), (Star r0))) (fun i -> Seq
            ((Event i), (Seq
            ((derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r0), (Star r0))))) [] (fun a0 _ ->
            Assoc ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r0), (Star r0))))
          (factor_seq_r_r af []
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (index_enum af) (fun a0 -> Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r0))) (Star r0))) (Cid Eps))
      (let b0 =
         nu
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0
       in
       if b0
       then ctrans1 af (Star r0) [] (Plus (Eps, (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))) (Plus
              (Eps, (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))) (Drop
              (r0,
              (Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0)))))), hd0)) (Cid (Plus (Eps,
              (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))))
       else ctrans1 af (Star r0) [] (Plus (Eps, (Seq (r0,
              (Star r0))))) (Plus (Eps, (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))) (Wrapinv
              r0)
              (cplus1 af Eps Eps [] (Seq (r0, (Star r0)))
                (Seq
                ((Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), (Star r0))) (Cid Eps)
                (ctrans1 af (Seq (r0, (Star r0))) [] (Seq
                  ((Plus (Empt,
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))), (Star r0))) (Seq
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0)))))), (Star r0)))
                  (cseq1 af r0 (Plus (Empt,
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))))) (Star r0) (Star
                    r0) [] hd0 (Cid (Star r0)))
                  (ctrans1 af (Seq ((Plus (Empt,
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))))), (Star r0))) []
                    (Plus ((Seq (Empt, (Star r0))), (Seq
                    ((Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r0)))))), (Star r0)))))
                    (Seq
                    ((Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r0)))))), (Star r0)))
                    (DistR (Empt,
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), (Star r0)))
                    (ctrans1 af (Plus ((Seq (Empt, (Star
                      r0))), (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))))
                      [] (Plus (Empt, (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))))
                      (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))
                      (cplus1 af (Seq (Empt, (Star r0))) Empt
                        [] (Seq
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))), (Star r0)))
                        (Seq
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))), (Star r0)))
                        (AbortL (Star r0)) (Cid (Seq
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))), (Star r0)))))
                      (UntagL (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))))))))
  in
  let rec f = function
  | Eps -> _evar_0_
  | Empt -> _evar_0_0
  | Event s -> _evar_0_1 s
  | Plus (r0, r1) -> _evar_0_2 r0 (f r0) r1 (f r1)
  | Seq (r0, r1) -> _evar_0_3 r0 (f r0) r1 (f r1)
  | Star r0 -> _evar_0_4 r0 (f r0)
  in f __top_assumption_

(** val derive_unfold_coerce2 :
    Finite.coq_type -> regex -> dsl **)

let derive_unfold_coerce2 af __top_assumption_ =
  let _evar_0_ =
    ctrans2 af (Plus (Eps,
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0), Empt))))))) [] (Plus (Eps, Empt)) Eps
      (ctrans2 af (Plus (Eps, Empt)) [] (Plus (Empt, Eps))
        Eps (UntagL Eps) (Retag (Eps, Empt)))
      (cplus1 af Eps Eps []
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0), Empt))))) Empt (Cid Eps)
        (ctrans1 af
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0), Empt))))) []
          (Coq_bigop.body Empt (index_enum af) (fun i ->
            BigBody (i, (fun x x0 -> Plus (x, x0)), true,
            Empt))) Empt
          (eq_big_plus_c af (index_enum af) (fun i -> Seq
            ((Event i), Empt)) (fun _ -> Empt) []
            (fun a0 _ -> AbortR (Event a0)))
          (plus_empt_l af
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) [] (index_enum af))))
  in
  let _evar_0_0 =
    ctrans1 af (Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) Empt),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 Empt)))))))) [] (Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) Empt),
      (Coq_bigop.body Empt (index_enum af) (fun i -> BigBody
        (i, (fun x x0 -> Plus (x, x0)), true, Empt))))) Empt
      (cplus2 af
        (o
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) Empt)
        (o
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) Empt) []
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 Empt))))))
        (Coq_bigop.body Empt (index_enum af) (fun i ->
          BigBody (i, (fun x x0 -> Plus (x, x0)), true,
          Empt)))
        (eq_big_plus_c af (index_enum af) (fun i -> Seq
          ((Event i),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) i Empt))) (fun _ -> Empt) [] (fun a0 _ ->
          AbortR (Event a0))) (Cid
        (o
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) Empt)))
      (ctrans1 af (Plus (Empt,
        (Coq_bigop.body Empt (index_enum af) (fun i ->
          BigBody (i, (fun x x0 -> Plus (x, x0)), true,
          Empt))))) []
        (Coq_bigop.body Empt (index_enum af) (fun i ->
          BigBody (i, (fun x x0 -> Plus (x, x0)), true,
          Empt))) Empt (UntagL
        (Coq_bigop.body Empt (index_enum af) (fun i ->
          BigBody (i, (fun x x0 -> Plus (x, x0)), true,
          Empt))))
        (plus_empt_l af
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) [] (index_enum af)))
  in
  let _evar_0_1 = fun s ->
    ctrans1 af (Plus (Empt,
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (if eq_op0
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) s a0
         then Eps
         else Empt)))))))) []
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (if eq_op0
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) s a0
         then Eps
         else Empt)))))) (Event s) (UntagL
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (if eq_op0
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) s a0
         then Eps
         else Empt)))))))
      (big_event_in_l af [] (Obj.magic index_enum af) s)
  in
  let _evar_0_2 = fun r0 hd0 r1 hd1 ->
    ctrans2 af (Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) (Plus (r0, r1))),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 (Plus (r0, r1)))))))))) [] (Plus ((Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) r0),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0)))))))), (Plus
      ((o
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) r1),
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0),
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r1)))))))))) (Plus (r0, r1))
      (cplus1 af (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)))))))) r0 [] (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1)))))))) r1 hd0 hd1)
      (ctrans2 af (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) (Plus (r0, r1))),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 (Plus (r0, r1)))))))))) [] (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0), (Plus
        ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0)))))), (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1)))))))))))) (Plus ((Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)))))))), (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1)))))))))) (Shuffleinv
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)))))), (Plus
        ((o
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r1),
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0),
          (derive
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r1))))))))))
        (ctrans1 af (Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) (Plus (r0, r1))),
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 (Plus (r0, r1)))))))))) [] (Plus
          ((Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) r0),
          (o
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) r1))),
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 (Plus (r0, r1)))))))))) (Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) r0), (Plus
          ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0)))))), (Plus
          ((o
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) r1),
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r1))))))))))))
          (cplus1 af
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) (Plus (r0, r1))) (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0),
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1))) []
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))
            (o_plus_l af r0 r1 []) (Cid
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))))
          (ctrans1 af (Plus ((Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0),
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1))),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1)))))))))) [] (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0), (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1)))))))))))) (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0), (Plus
            ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0)))))), (Plus
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r1)))))))))))) (Shuffle
            ((o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r0),
            (o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1),
            (Coq_bigop.body Empt (index_enum af) (fun a0 ->
              BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
              (Seq ((Event a0),
              (derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 (Plus (r0, r1))))))))))
            (cplus1 af
              (o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r0)
              (o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r0) [] (Plus
              ((o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1),
              (Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 (Plus (r0, r1)))))))))) (Plus
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Plus
              ((o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1),
              (Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r1)))))))))) (Cid
              (o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r0))
              (ctrans2 af (Plus
                ((o
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) r1),
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 (Plus (r0, r1)))))))))) [] (Plus
                ((o
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) r1), (Plus
                ((Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1)))))),
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))))))) (Plus
                ((Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), (Plus
                ((o
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) r1),
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r1))))))))))
                (ctrans2 af (Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1), (Plus
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))))) [] (Plus ((Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))) (Plus
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0)))))), (Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))))))) (Retag ((Plus
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))) (Shuffleinv
                  ((o
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) r1),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r1)))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))))
                (cplus1 af
                  (o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1)
                  (o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1) []
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 (Plus (r0, r1)))))))) (Plus
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))),
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))) (Cid
                  (o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1))
                  (ctrans1 af
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (Plus
                      ((derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r1)))))))) []
                    (Coq_bigop.body Empt (index_enum af)
                      (fun i -> BigBody (i, (fun x x0 -> Plus
                      (x, x0)), true, (Plus ((Seq ((Event i),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) i r0))), (Seq ((Event i),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) i r1)))))))) (Plus
                    ((Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))),
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0))))))))
                    (eq_big_plus_c af (index_enum af)
                      (fun i -> Seq ((Event i), (Plus
                      ((derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) i r0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) i r1))))) (fun a0 -> Plus ((Seq
                      ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0))), (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r1))))) [] (fun a0 _ ->
                      DistL ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r1))))
                    (ctrans1 af
                      (Coq_bigop.body Empt (index_enum af)
                        (fun i -> BigBody (i, (fun x x0 ->
                        Plus (x, x0)), true, (Plus ((Seq
                        ((Event i),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) i r0))), (Seq ((Event i),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) i r1)))))))) [] (Plus
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))),
                      (Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))))) (Plus
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))),
                      (Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0))))))))
                      (ctrans1 af
                        (Coq_bigop.body Empt (index_enum af)
                          (fun i -> BigBody (i, (fun x x0 ->
                          Plus (x, x0)), true, (Plus ((Seq
                          ((Event i),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) i r0))), (Seq ((Event i),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) i r1)))))))) [] (Plus
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))),
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))))))) (Plus
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))),
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))))))))
                        (split_plus_l af []
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) (index_enum af) (fun a0 ->
                          Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))) (fun a0 -> Seq
                          ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))) (Retag
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))),
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))))))))
                      (cplus1 af
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1))))))
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))))) []
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))))))
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))) (Cid
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1))))))) (Cid
                        (Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0))))))))))))))))
  in
  let _evar_0_3 = fun r0 hd0 r1 hd1 ->
    let b0 =
      nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) r0
    in
    if b0
    then ctrans1 af (Plus
           ((o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1),
           (Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0), (Plus ((Seq
             ((derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r0), r1)),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r1)))))))))) [] (Plus
           ((o
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) r1),
           (Coq_bigop.body Empt (index_enum af) (fun i ->
             BigBody (i, (fun x x0 -> Plus (x, x0)), true,
             (Plus ((Seq ((Seq ((Event i),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r0))), r1)), (Seq ((Event i),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r1)))))))))) (Seq (r0, r1))
           (cplus2 af
             (o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1)
             (o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1) []
             (Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0), (Plus ((Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0), r1)),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r1))))))))
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Plus ((Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)), (Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r1))))))))
             (eq_big_plus_c af (index_enum af) (fun i -> Seq
               ((Event i), (Plus ((Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) i r0), r1)),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r1))))) (fun a0 -> Plus ((Seq ((Seq
               ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0))), r1)), (Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r1))))) [] (fun a0 _ ->
               ctrans1 af (Seq ((Event a0), (Plus ((Seq
                 ((derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0), r1)),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))) [] (Plus ((Seq ((Event
                 a0), (Seq
                 ((derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0), r1)))), (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))) (Plus ((Seq ((Seq ((Event
                 a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0))), r1)), (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))) (DistL ((Event a0), (Seq
                 ((derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0), r1)),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1)))
                 (cplus1 af (Seq ((Event a0), (Seq
                   ((derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0), r1)))) (Seq ((Seq ((Event
                   a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0))), r1)) [] (Seq ((Event
                   a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))) (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))) (Associnv ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0), r1)) (Cid (Seq ((Event
                   a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))))))) (Cid
             (o
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) r1)))
           (ctrans1 af (Plus
             ((o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r1),
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Plus ((Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)), (Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r1)))))))))) [] (Plus
             ((o
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) r1), (Plus ((Seq
             ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0)))))), r1)),
             (Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r1)))))))))) (Seq (r0, r1))
             (cplus2 af
               (o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1)
               (o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1) []
               (Coq_bigop.body Empt (index_enum af) (fun i ->
                 BigBody (i, (fun x x0 -> Plus (x, x0)),
                 true, (Plus ((Seq ((Seq ((Event i),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) i r0))), r1)), (Seq ((Event i),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) i r1)))))))) (Plus ((Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1)),
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1))))))))
               (ctrans1 af
                 (Coq_bigop.body Empt (index_enum af)
                   (fun i -> BigBody (i, (fun x x0 -> Plus
                   (x, x0)), true, (Plus ((Seq ((Seq ((Event
                   i),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) i r0))), r1)), (Seq ((Event i),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) i r1)))))))) [] (Plus
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0))), r1))))),
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1)))))))) (Plus ((Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)),
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))))))))
                 (split_plus_l af []
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) (index_enum af) (fun a0 -> Seq ((Seq
                   ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0))), r1)) (fun a0 -> Seq
                   ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1))))
                 (cplus1 af
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Seq ((Event
                     a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0))), r1))))) (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)) []
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))
                   (factor_seq_r_l af []
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) (index_enum af) (fun a0 -> Seq
                     ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0))) r1) (Cid
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1))))))))) (Cid
               (o
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) r1)))
             (ctrans2 af (Plus
               ((o
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) r1), (Plus ((Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1)),
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r1)))))))))) [] (Seq ((Plus (Eps,
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))))), r1)) (Seq (r0, r1))
               (cseq1 af (Plus (Eps,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))) r0 r1 r1 [] hd0 (Cid
                 r1))
               (ctrans2 af (Plus
                 ((o
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) r1), (Plus ((Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)),
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r1)))))))))) [] (Plus ((Seq
                 (Eps, r1)), (Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)))) (Seq ((Plus
                 (Eps,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))), r1)) (DistRinv
                 (Eps,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), r1))
                 (ctrans2 af (Plus
                   ((o
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) r1), (Plus ((Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)),
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))))))) [] (Plus ((Plus
                   ((o
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) r1),
                   (Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r1)))))))), (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) (Plus ((Seq
                   (Eps, r1)), (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1))))
                   (cplus1 af (Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))))) (Seq (Eps, r1))
                     [] (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)) (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))
                     (ctrans2 af (Plus
                       ((o
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) r1),
                       (Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))))) [] r1 (Seq
                       (Eps, r1)) (Projinv r1) hd1) (Cid (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))))
                   (ctrans2 af (Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1), (Plus ((Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))))))) [] (Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1), (Plus
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r1)))))), (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)))))) (Plus
                     ((Plus
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))))), (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))))
                     (Shuffleinv
                     ((o
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) r1),
                     (Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r1)))))), (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1))))
                     (cplus1 af
                       (o
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) r1)
                       (o
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) r1) [] (Plus ((Seq
                       ((Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))), r1)),
                       (Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r1)))))))) (Plus
                       ((Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r1)))))), (Seq
                       ((Coq_bigop.body Empt (index_enum af)
                          (fun a0 -> BigBody (a0,
                          (fun x x0 -> Plus (x, x0)), true,
                          (Seq ((Event a0),
                          (derive
                            (Finite.Exports.fintype_Finite__to__eqtype_Equality
                              af) a0 r0)))))), r1)))) (Cid
                       (o
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) r1))
                       (ctrans1 af (Plus ((Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)),
                         (Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))))) [] (Plus
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r1)))))), (Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)))) (Plus
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r1)))))), (Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1))))
                         (Retag ((Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1)),
                         (Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r1)))))))) (Cid (Plus
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r1)))))), (Seq
                         ((Coq_bigop.body Empt
                            (index_enum af) (fun a0 ->
                            BigBody (a0, (fun x x0 -> Plus
                            (x, x0)), true, (Seq ((Event a0),
                            (derive
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af) a0 r0)))))), r1))))))))))))
    else ctrans1 af (Plus (Empt,
           (Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0), (Seq
             ((derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r0), r1))))))))) [] (Plus (Empt,
           (Coq_bigop.body Empt (index_enum af) (fun i ->
             BigBody (i, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Seq ((Event i),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r0))), r1))))))) (Seq (r0, r1))
           (cplus2 af Empt Empt []
             (Coq_bigop.body Empt (index_enum af) (fun a0 ->
               BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Event a0), (Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0), r1)))))))
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1)))))
             (eq_big_plus_c af (index_enum af) (fun i -> Seq
               ((Event i), (Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) i r0), r1)))) (fun a0 -> Seq ((Seq
               ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0))), r1)) [] (fun a0 _ ->
               Associnv ((Event a0),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0), r1))) (Cid Empt))
           (ctrans1 af (Plus (Empt,
             (Coq_bigop.body Empt (index_enum af) (fun i ->
               BigBody (i, (fun x x0 -> Plus (x, x0)), true,
               (Seq ((Seq ((Event i),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) i r0))), r1))))))) [] (Plus (Empt,
             (Seq
             ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
                BigBody (a0, (fun x x0 -> Plus (x, x0)),
                true, (Seq ((Event a0),
                (derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r0)))))), r1)))) (Seq (r0, r1))
             (cplus2 af Empt Empt []
               (Coq_bigop.body Empt (index_enum af) (fun i ->
                 BigBody (i, (fun x x0 -> Plus (x, x0)),
                 true, (Seq ((Seq ((Event i),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) i r0))), r1))))) (Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1))
               (factor_seq_r_l af []
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) (index_enum af) (fun a0 -> Seq ((Event
                 a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0))) r1) (Cid Empt))
             (ctrans2 af (Plus (Empt, (Seq
               ((Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))), r1)))) [] (Seq ((Plus
               (Empt,
               (Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))))), r1)) (Seq (r0, r1))
               (cseq1 af (Plus (Empt,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))) r0 r1 r1 [] hd0 (Cid
                 r1))
               (ctrans2 af (Plus (Empt, (Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)))) [] (Plus
                 ((Seq (Empt, r1)), (Seq
                 ((Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))), r1)))) (Seq ((Plus
                 (Empt,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))))), r1)) (DistRinv
                 (Empt,
                 (Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), r1))
                 (ctrans2 af (Plus (Empt, (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) [] (Plus
                   (Empt, (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))) (Plus ((Seq
                   (Empt, r1)), (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1))))
                   (cplus1 af Empt (Seq (Empt, r1)) [] (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)) (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)) (AbortLinv
                     r1) (Cid (Seq
                     ((Coq_bigop.body Empt (index_enum af)
                        (fun a0 -> BigBody (a0, (fun x x0 ->
                        Plus (x, x0)), true, (Seq ((Event
                        a0),
                        (derive
                          (Finite.Exports.fintype_Finite__to__eqtype_Equality
                            af) a0 r0)))))), r1)))) (Cid
                   (Plus (Empt, (Seq
                   ((Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), r1)))))))))
  in
  let _evar_0_4 = fun r0 hd0 ->
    ctrans1 af (Plus (Eps,
      (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
        (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
        a0), (Seq
        ((derive
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r0), (Star r0)))))))))) [] (Plus (Eps,
      (Seq
      ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
         BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
         ((Event a0),
         (derive
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r0)))))), (Star r0))))) (Star r0)
      (cplus2 af Eps Eps []
        (Coq_bigop.body Empt (index_enum af) (fun a0 ->
          BigBody (a0, (fun x x0 -> Plus (x, x0)), true, (Seq
          ((Event a0), (Seq
          ((derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0), (Star r0)))))))) (Seq
        ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0)))))), (Star r0)))
        (ctrans1 af
          (Coq_bigop.body Empt (index_enum af) (fun a0 ->
            BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Event a0), (Seq
            ((derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0), (Star r0)))))))) []
          (Coq_bigop.body Empt (index_enum af) (fun i ->
            BigBody (i, (fun x x0 -> Plus (x, x0)), true,
            (Seq ((Seq ((Event i),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) i r0))), (Star r0)))))) (Seq
          ((Coq_bigop.body Empt (index_enum af) (fun a0 ->
             BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
             (Seq ((Event a0),
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0)))))), (Star r0)))
          (eq_big_plus_c af (index_enum af) (fun i -> Seq
            ((Event i), (Seq
            ((derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) i r0), (Star r0))))) (fun a0 -> Seq
            ((Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r0))), (Star r0))) [] (fun a0 _ ->
            Associnv ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r0), (Star r0))))
          (factor_seq_r_l af []
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (index_enum af) (fun a0 -> Seq ((Event a0),
            (derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r0))) (Star r0))) (Cid Eps))
      (let b0 =
         nu
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) r0
       in
       if b0
       then ctrans2 af (Plus (Eps, (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))) [] (Plus
              (Eps, (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))) (Star r0)
              (dropinv af [] r0
                (Coq_bigop.body Empt (index_enum af)
                  (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                  (x, x0)), true, (Seq ((Event a0),
                  (derive
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r0)))))) hd0) (Cid (Plus (Eps,
              (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))))
       else ctrans2 af (Plus (Eps, (Seq
              ((Coq_bigop.body Empt (index_enum af)
                 (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                 (x, x0)), true, (Seq ((Event a0),
                 (derive
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r0)))))), (Star r0))))) [] (Plus
              (Eps, (Seq (r0, (Star r0))))) (Star r0) (Wrap
              r0)
              (cplus1 af Eps Eps [] (Seq
                ((Coq_bigop.body Empt (index_enum af)
                   (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                   (x, x0)), true, (Seq ((Event a0),
                   (derive
                     (Finite.Exports.fintype_Finite__to__eqtype_Equality
                       af) a0 r0)))))), (Star r0))) (Seq (r0,
                (Star r0))) (Cid Eps)
                (ctrans2 af (Seq
                  ((Coq_bigop.body Empt (index_enum af)
                     (fun a0 -> BigBody (a0, (fun x x0 ->
                     Plus (x, x0)), true, (Seq ((Event a0),
                     (derive
                       (Finite.Exports.fintype_Finite__to__eqtype_Equality
                         af) a0 r0)))))), (Star r0))) [] (Seq
                  ((Plus (Empt,
                  (Coq_bigop.body Empt (index_enum af)
                    (fun a0 -> BigBody (a0, (fun x x0 -> Plus
                    (x, x0)), true, (Seq ((Event a0),
                    (derive
                      (Finite.Exports.fintype_Finite__to__eqtype_Equality
                        af) a0 r0)))))))), (Star r0))) (Seq
                  (r0, (Star r0)))
                  (cseq1 af (Plus (Empt,
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))))) r0 (Star r0)
                    (Star r0) [] hd0 (Cid (Star r0)))
                  (ctrans2 af (Seq
                    ((Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r0)))))), (Star r0))) []
                    (Plus ((Seq (Empt, (Star r0))), (Seq
                    ((Coq_bigop.body Empt (index_enum af)
                       (fun a0 -> BigBody (a0, (fun x x0 ->
                       Plus (x, x0)), true, (Seq ((Event a0),
                       (derive
                         (Finite.Exports.fintype_Finite__to__eqtype_Equality
                           af) a0 r0)))))), (Star r0)))))
                    (Seq ((Plus (Empt,
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))))), (Star r0)))
                    (DistRinv (Empt,
                    (Coq_bigop.body Empt (index_enum af)
                      (fun a0 -> BigBody (a0, (fun x x0 ->
                      Plus (x, x0)), true, (Seq ((Event a0),
                      (derive
                        (Finite.Exports.fintype_Finite__to__eqtype_Equality
                          af) a0 r0)))))), (Star r0)))
                    (ctrans2 af (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0))) []
                      (Plus (Empt, (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))))
                      (Plus ((Seq (Empt, (Star r0))), (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))))
                      (cplus1 af Empt (Seq (Empt, (Star r0)))
                        [] (Seq
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))), (Star r0)))
                        (Seq
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))), (Star r0)))
                        (AbortLinv (Star r0)) (Cid (Seq
                        ((Coq_bigop.body Empt (index_enum af)
                           (fun a0 -> BigBody (a0,
                           (fun x x0 -> Plus (x, x0)), true,
                           (Seq ((Event a0),
                           (derive
                             (Finite.Exports.fintype_Finite__to__eqtype_Equality
                               af) a0 r0)))))), (Star r0)))))
                      (UntagLinv (Seq
                      ((Coq_bigop.body Empt (index_enum af)
                         (fun a0 -> BigBody (a0, (fun x x0 ->
                         Plus (x, x0)), true, (Seq ((Event
                         a0),
                         (derive
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af) a0 r0)))))), (Star r0)))))))))
  in
  let rec f = function
  | Eps -> _evar_0_
  | Empt -> _evar_0_0
  | Event s -> _evar_0_1 s
  | Plus (r0, r1) -> _evar_0_2 r0 (f r0) r1 (f r1)
  | Seq (r0, r1) -> _evar_0_3 r0 (f r0) r1 (f r1)
  | Star r0 -> _evar_0_4 r0 (f r0)
  in f __top_assumption_

(** val derive_unfold_coerce_l :
    Finite.coq_type -> regex -> dsl **)

let derive_unfold_coerce_l =
  derive_unfold_coerce

(** val derive_unfold_coerce_r :
    Finite.coq_type -> regex -> dsl **)

let derive_unfold_coerce_r =
  derive_unfold_coerce2

(** val empt_Eps :
    Finite.coq_type -> (regex * regex) list -> dsl **)

let empt_Eps af l =
  ctrans1 af Empt l (Plus (Empt, Eps)) Eps (TagL (Empt, Eps))
    (ctrans1 af (Plus (Empt, Eps)) l (Plus (Eps, Empt)) Eps
      (Retag (Empt, Eps)) (Dsl_fix ((Plus (Eps, Empt)), Eps,
      (Dsl_fix ((Plus (Eps, Empt)), Eps, (Dsl_fix ((Plus
      (Eps, Empt)), Eps, (Ctrans ((Plus (Eps, Empt)), (Plus
      (Empt, Eps)), Eps, (Retag (Eps, Empt)), (UntagL
      Eps))))))))))

(** val o_lP :
    Finite.coq_type -> regex list -> regex list ->
    (regex * regex) list -> dsl **)

let o_lP af l l' l0 =
  let b0 =
    has
      (nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af)) l
  in
  if b0
  then Cid Eps
  else let b1 =
         has
           (nu
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af)) l'
       in
       if b1 then empt_Eps af l0 else Cid Empt

(** val c_eq_cat1 :
    Finite.coq_type -> regex list -> regex list ->
    (regex * regex) list -> dsl **)

let c_eq_cat1 af __top_assumption_ =
  let _evar_0_ = fun l1 _ -> UntagLinv
    (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
      (fun x x0 -> Plus (x, x0)), true, i)))
  in
  let _evar_0_0 = fun a0 l x l1 l0 ->
    ctrans2 af (Plus (a0,
      (Coq_bigop.body Empt (cat l l1) (fun j -> BigBody (j,
        (fun x0 x1 -> Plus (x0, x1)), true, j))))) l0 (Plus
      (a0, (Plus
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x0 x1 -> Plus (x0, x1)), true, j))),
      (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
        (fun x0 x1 -> Plus (x0, x1)), true, i))))))) (Plus
      ((Plus (a0,
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x0 x1 -> Plus (x0, x1)), true, j))))),
      (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
        (fun x0 x1 -> Plus (x0, x1)), true, i)))))
      (Shuffleinv (a0,
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x0 x1 -> Plus (x0, x1)), true, j))),
      (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
        (fun x0 x1 -> Plus (x0, x1)), true, i)))))
      (cplus1 af a0 a0 l0
        (Coq_bigop.body Empt (cat l l1) (fun j -> BigBody (j,
          (fun x0 x1 -> Plus (x0, x1)), true, j))) (Plus
        ((Coq_bigop.body Empt l (fun j -> BigBody (j,
           (fun x0 x1 -> Plus (x0, x1)), true, j))),
        (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
          (fun x0 x1 -> Plus (x0, x1)), true, i))))) (Cid a0)
        (x l1 l0))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f __top_assumption_

(** val c_eq_cat2 :
    Finite.coq_type -> regex list -> regex list ->
    (regex * regex) list -> dsl **)

let c_eq_cat2 af __top_assumption_ =
  let _evar_0_ = fun l1 _ -> UntagL
    (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
      (fun x x0 -> Plus (x, x0)), true, i)))
  in
  let _evar_0_0 = fun a0 l x l1 l0 ->
    ctrans1 af (Plus ((Plus (a0,
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x0 x1 -> Plus (x0, x1)), true, j))))),
      (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
        (fun x0 x1 -> Plus (x0, x1)), true, i))))) l0 (Plus
      (a0, (Plus
      ((Coq_bigop.body Empt l (fun j -> BigBody (j,
         (fun x0 x1 -> Plus (x0, x1)), true, j))),
      (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
        (fun x0 x1 -> Plus (x0, x1)), true, i))))))) (Plus
      (a0,
      (Coq_bigop.body Empt (cat l l1) (fun j -> BigBody (j,
        (fun x0 x1 -> Plus (x0, x1)), true, j))))) (Shuffle
      (a0,
      (Coq_bigop.body Empt l (fun j -> BigBody (j,
        (fun x0 x1 -> Plus (x0, x1)), true, j))),
      (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
        (fun x0 x1 -> Plus (x0, x1)), true, i)))))
      (cplus1 af a0 a0 l0 (Plus
        ((Coq_bigop.body Empt l (fun j -> BigBody (j,
           (fun x0 x1 -> Plus (x0, x1)), true, j))),
        (Coq_bigop.body Empt l1 (fun i -> BigBody (i,
          (fun x0 x1 -> Plus (x0, x1)), true, i)))))
        (Coq_bigop.body Empt (cat l l1) (fun j -> BigBody (j,
          (fun x0 x1 -> Plus (x0, x1)), true, j))) (Cid a0)
        (x l1 l0))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f __top_assumption_

(** val c_eq_derive_pd_l1 :
    Finite.coq_type -> regex -> (regex * regex) list ->
    Equality.sort -> dsl **)

let c_eq_derive_pd_l1 af __top_assumption_ =
  let _evar_0_ = fun _ _ -> Cid Empt in
  let _evar_0_0 = fun _ _ -> Cid Empt in
  let _evar_0_1 = fun s _ a0 ->
    let b0 =
      eq_op0
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) s a0
    in
    if b0 then TagL (Eps, Empt) else Cid Empt
  in
  let _evar_0_2 = fun r x r0 x0 l a0 ->
    ctrans2 af (Plus
      ((derive
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) a0 r),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 r0))) l (Plus
      ((Coq_bigop.body Empt
         (pd
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r) (fun i -> BigBody (i, (fun x1 x2 ->
         Plus (x1, x2)), true, i))),
      (Coq_bigop.body Empt
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0) (fun i -> BigBody (i, (fun x1 x2 ->
        Plus (x1, x2)), true, i)))))
      (Coq_bigop.body Empt
        (cat
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r)
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)) (fun i -> BigBody (i, (fun x1 x2 ->
        Plus (x1, x2)), true, i)))
      (c_eq_cat2 af
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r)
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0) l)
      (cplus1 af
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r)
        (Coq_bigop.body Empt
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r) (fun i -> BigBody (i, (fun x1 x2 ->
          Plus (x1, x2)), true, i))) l
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0)
        (Coq_bigop.body Empt
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0) (fun i -> BigBody (i, (fun x1 x2 ->
          Plus (x1, x2)), true, i))) (x l a0) (x0 l a0))
  in
  let _evar_0_3 = fun r x r0 x0 l a0 ->
    let b0 =
      nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) r
    in
    if b0
    then ctrans2 af (Plus ((Seq
           ((derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r), r0)),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0))) l (Plus
           ((Coq_bigop.body Empt
              (map (fun x1 -> Seq (x1, r0))
                (pd
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r)) (fun i -> BigBody (i,
              (fun x1 x2 -> Plus (x1, x2)), true, i))),
           (Coq_bigop.body Empt
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0) (fun i -> BigBody (i,
             (fun x1 x2 -> Plus (x1, x2)), true, i)))))
           (Coq_bigop.body Empt
             (cat
               (map (fun x1 -> Seq (x1, r0))
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r))
               (pd
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0)) (fun i -> BigBody (i,
             (fun x1 x2 -> Plus (x1, x2)), true, i)))
           (c_eq_cat2 af
             (map (fun x1 -> Seq (x1, r0))
               (pd
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r))
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0) l)
           (cplus1 af (Seq
             ((derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r), r0))
             (Coq_bigop.body Empt
               (map (fun x1 -> Seq (x1, r0))
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r)) (fun i -> BigBody (i,
               (fun x1 x2 -> Plus (x1, x2)), true, i))) l
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0)
             (Coq_bigop.body Empt
               (pd
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0) (fun i -> BigBody (i,
               (fun x1 x2 -> Plus (x1, x2)), true, i)))
             (ctrans2 af (Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r), r0)) l (Seq
               ((Coq_bigop.body Empt
                  (pd
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r) (fun a1 -> BigBody (a1,
                  (fun x1 x2 -> Plus (x1, x2)), true, a1))),
               r0))
               (Coq_bigop.body Empt
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r) (fun a1 -> BigBody (a1,
                 (fun x1 x2 -> Plus (x1, x2)), true, (Seq
                 (a1, r0)))))
               (factor_seq_r_r af l
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af))
                 (Obj.magic pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r) (fun a1 -> Obj.magic a1) r0)
               (Cseq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r),
               (Coq_bigop.body Empt
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r) (fun a1 -> BigBody (a1,
                 (fun x1 x2 -> Plus (x1, x2)), true, a1))),
               r0, r0, (x l a0), (Cid r0)))) (x0 l a0))
    else ctrans2 af (Seq
           ((derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r), r0)) l (Seq
           ((Coq_bigop.body Empt
              (pd
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r) (fun a1 -> BigBody (a1,
              (fun x1 x2 -> Plus (x1, x2)), true, a1))), r0))
           (Coq_bigop.body Empt
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r) (fun a1 -> BigBody (a1,
             (fun x1 x2 -> Plus (x1, x2)), true, (Seq (a1,
             r0)))))
           (factor_seq_r_r af l
             (regex_regex__canonical__eqtype_Equality
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af))
             (Obj.magic pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r) (fun a1 -> Obj.magic a1) r0) (Cseq
           ((derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r),
           (Coq_bigop.body Empt
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r) (fun a1 -> BigBody (a1,
             (fun x1 x2 -> Plus (x1, x2)), true, a1))), r0,
           r0, (x l a0), (Cid r0)))
  in
  let _evar_0_4 = fun r x l a0 ->
    ctrans2 af (Seq
      ((derive
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) a0 r), (Star r))) l (Seq
      ((Coq_bigop.body Empt
         (pd
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r) (fun a1 -> BigBody (a1, (fun x0 x1 ->
         Plus (x0, x1)), true, a1))), (Star r)))
      (Coq_bigop.body Empt
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r) (fun a1 -> BigBody (a1, (fun x0 x1 ->
        Plus (x0, x1)), true, (Seq (a1, (Star r))))))
      (factor_seq_r_r af l
        (regex_regex__canonical__eqtype_Equality
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af))
        (Obj.magic pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r) (fun a1 -> Obj.magic a1) (Star r))
      (Cseq
      ((derive
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) a0 r),
      (Coq_bigop.body Empt
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r) (fun a1 -> BigBody (a1, (fun x0 x1 ->
        Plus (x0, x1)), true, a1))), (Star r), (Star r),
      (x l a0), (Cid (Star r))))
  in
  let rec f = function
  | Eps -> _evar_0_
  | Empt -> _evar_0_0
  | Event s -> _evar_0_1 s
  | Plus (r0, r1) -> _evar_0_2 r0 (f r0) r1 (f r1)
  | Seq (r0, r1) -> _evar_0_3 r0 (f r0) r1 (f r1)
  | Star r0 -> _evar_0_4 r0 (f r0)
  in f __top_assumption_

(** val c_eq_derive_pd_l2 :
    Finite.coq_type -> regex -> (regex * regex) list ->
    Equality.sort -> dsl **)

let c_eq_derive_pd_l2 af __top_assumption_ =
  let _evar_0_ = fun _ _ -> Cid Empt in
  let _evar_0_0 = fun _ _ -> Cid Empt in
  let _evar_0_1 = fun s l a0 ->
    let b0 =
      eq_op0
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 s
    in
    if b0
    then ctrans1 af (Plus (Eps, Empt)) l (Plus (Empt, Eps))
           Eps (Retag (Eps, Empt)) (UntagL Eps)
    else Cid Empt
  in
  let _evar_0_2 = fun r x r0 x0 l a0 ->
    ctrans1 af
      (Coq_bigop.body Empt
        (cat
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r)
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0)) (fun i -> BigBody (i, (fun x1 x2 ->
        Plus (x1, x2)), true, i))) l (Plus
      ((Coq_bigop.body Empt
         (pd
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r) (fun i -> BigBody (i, (fun x1 x2 ->
         Plus (x1, x2)), true, i))),
      (Coq_bigop.body Empt
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0) (fun i -> BigBody (i, (fun x1 x2 ->
        Plus (x1, x2)), true, i))))) (Plus
      ((derive
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) a0 r),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 r0)))
      (c_eq_cat1 af
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r)
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0) l)
      (cplus1 af
        (Coq_bigop.body Empt
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r) (fun i -> BigBody (i, (fun x1 x2 ->
          Plus (x1, x2)), true, i)))
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r) l
        (Coq_bigop.body Empt
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0 r0) (fun i -> BigBody (i, (fun x1 x2 ->
          Plus (x1, x2)), true, i)))
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r0) (x l a0) (x0 l a0))
  in
  let _evar_0_3 = fun r x r0 x0 l a0 ->
    let b0 =
      nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) r
    in
    if b0
    then ctrans1 af
           (Coq_bigop.body Empt
             (cat
               (map (fun x1 -> Seq (x1, r0))
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r))
               (pd
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0)) (fun i -> BigBody (i,
             (fun x1 x2 -> Plus (x1, x2)), true, i))) l (Plus
           ((Coq_bigop.body Empt
              (map (fun x1 -> Seq (x1, r0))
                (pd
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r)) (fun i -> BigBody (i,
              (fun x1 x2 -> Plus (x1, x2)), true, i))),
           (Coq_bigop.body Empt
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0) (fun i -> BigBody (i,
             (fun x1 x2 -> Plus (x1, x2)), true, i))))) (Plus
           ((Seq
           ((derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r), r0)),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r0)))
           (c_eq_cat1 af
             (map (fun x1 -> Seq (x1, r0))
               (pd
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r))
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0) l)
           (cplus1 af
             (Coq_bigop.body Empt
               (map (fun x1 -> Seq (x1, r0))
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r)) (fun i -> BigBody (i,
               (fun x1 x2 -> Plus (x1, x2)), true, i))) (Seq
             ((derive
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r), r0)) l
             (Coq_bigop.body Empt
               (pd
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r0) (fun i -> BigBody (i,
               (fun x1 x2 -> Plus (x1, x2)), true, i)))
             (derive
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r0)
             (ctrans1 af
               (Coq_bigop.body Empt
                 (pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r) (fun a1 -> BigBody (a1,
                 (fun x1 x2 -> Plus (x1, x2)), true, (Seq
                 (a1, r0))))) l (Seq
               ((Coq_bigop.body Empt
                  (pd
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r) (fun a1 -> BigBody (a1,
                  (fun x1 x2 -> Plus (x1, x2)), true, a1))),
               r0)) (Seq
               ((derive
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a0 r), r0))
               (factor_seq_r_l af l
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af))
                 (Obj.magic pd
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af) a0 r) (fun a1 -> Obj.magic a1) r0)
               (Cseq
               ((Coq_bigop.body Empt
                  (pd
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af) a0 r) (fun a1 -> BigBody (a1,
                  (fun x1 x2 -> Plus (x1, x2)), true, a1))),
               (derive
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af) a0 r), r0, r0, (x l a0), (Cid r0))))
             (x0 l a0))
    else ctrans1 af
           (Coq_bigop.body Empt
             (pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r) (fun a1 -> BigBody (a1,
             (fun x1 x2 -> Plus (x1, x2)), true, (Seq (a1,
             r0))))) l (Seq
           ((Coq_bigop.body Empt
              (pd
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r) (fun a1 -> BigBody (a1,
              (fun x1 x2 -> Plus (x1, x2)), true, a1))), r0))
           (Seq
           ((derive
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0 r), r0))
           (factor_seq_r_l af l
             (regex_regex__canonical__eqtype_Equality
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af))
             (Obj.magic pd
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 r) (fun a1 -> Obj.magic a1) r0) (Cseq
           ((Coq_bigop.body Empt
              (pd
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a0 r) (fun a1 -> BigBody (a1,
              (fun x1 x2 -> Plus (x1, x2)), true, a1))),
           (derive
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) a0 r), r0, r0, (x l a0), (Cid r0)))
  in
  let _evar_0_4 = fun r x l a0 ->
    ctrans1 af
      (Coq_bigop.body Empt
        (pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r) (fun a1 -> BigBody (a1, (fun x0 x1 ->
        Plus (x0, x1)), true, (Seq (a1, (Star r)))))) l (Seq
      ((Coq_bigop.body Empt
         (pd
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r) (fun a1 -> BigBody (a1, (fun x0 x1 ->
         Plus (x0, x1)), true, a1))), (Star r))) (Seq
      ((derive
         (Finite.Exports.fintype_Finite__to__eqtype_Equality
           af) a0 r), (Star r)))
      (factor_seq_r_l af l
        (regex_regex__canonical__eqtype_Equality
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af))
        (Obj.magic pd
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 r) (fun a1 -> Obj.magic a1) (Star r))
      (Cseq
      ((Coq_bigop.body Empt
         (pd
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) a0 r) (fun a1 -> BigBody (a1, (fun x0 x1 ->
         Plus (x0, x1)), true, a1))),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0 r), (Star r), (Star r), (x l a0), (Cid (Star
      r))))
  in
  let rec f = function
  | Eps -> _evar_0_
  | Empt -> _evar_0_0
  | Event s -> _evar_0_1 s
  | Plus (r0, r1) -> _evar_0_2 r0 (f r0) r1 (f r1)
  | Seq (r0, r1) -> _evar_0_3 r0 (f r0) r1 (f r1)
  | Star r0 -> _evar_0_4 r0 (f r0)
  in f __top_assumption_

(** val c_eq_undup1 :
    Finite.coq_type -> Equality.sort list -> (regex * regex)
    list -> dsl **)

let c_eq_undup1 af __top_assumption_ =
  let _evar_0_ = fun _ -> Cid
    (Coq_bigop.body Empt [] (fun i -> BigBody (i,
      (fun x x0 -> Plus (x, x0)), true, i)))
  in
  let _evar_0_0 = fun a0 l x l0 ->
    let b0 =
      in_mem a0
        (mem
          (seq_predType
            (regex_regex__canonical__eqtype_Equality
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af))) l)
    in
    if b0
    then ctrans2 af
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun i -> BigBody (i,
             (fun x0 x1 -> Plus (x0, x1)), true, i))) l0
           (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun i -> BigBody (i,
             (fun x0 x1 -> Plus (x0, x1)), true, i))))) (Plus
           ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j)))))
           (cplus1 af (Obj.magic a0) (Obj.magic a0) l0
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun i -> BigBody (i,
               (fun x0 x1 -> Plus (x0, x1)), true, i)))
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j))) (Cid (Obj.magic a0)) (x l0))
           (let _evar_0_0 = fun _ -> assert false
              (* absurd case *)
            in
            let _evar_0_1 = fun a1 l1 x0 a2 ->
              let e =
                eqVneq
                  (regex_regex__canonical__eqtype_Equality
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af)) a2 a1
              in
              (match e with
               | EqNotNeq ->
                 let b1 =
                   in_mem a1
                     (mem
                       (seq_predType
                         (regex_regex__canonical__eqtype_Equality
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af))) l1)
                 in
                 if b1
                 then x0 a1 __
                 else ctrans2 af (Plus ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))) l0 (Plus
                        ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))) (Plus ((Obj.magic a1),
                        (Plus ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j)))))))
                        (ctrans2 af (Plus ((Obj.magic a1),
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j))))) l0 (Plus ((Plus
                          ((Obj.magic a1), (Obj.magic a1))),
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j))))) (Plus
                          ((Obj.magic a1), (Plus
                          ((Obj.magic a1),
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j))))))) (Shuffle
                          ((Obj.magic a1), (Obj.magic a1),
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j)))))
                          (cplus1 af (Obj.magic a1) (Plus
                            ((Obj.magic a1), (Obj.magic a1)))
                            l0
                            (Coq_bigop.body Empt
                              (Obj.magic undup
                                (regex_regex__canonical__eqtype_Equality
                                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                    af)) l1) (fun j ->
                              BigBody (j, (fun x1 x2 -> Plus
                              (x1, x2)), true, j)))
                            (Coq_bigop.body Empt
                              (Obj.magic undup
                                (regex_regex__canonical__eqtype_Equality
                                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                    af)) l1) (fun j ->
                              BigBody (j, (fun x1 x2 -> Plus
                              (x1, x2)), true, j))) (TagL
                            ((Obj.magic a1), (Obj.magic a1)))
                            (Cid
                            (Coq_bigop.body Empt
                              (Obj.magic undup
                                (regex_regex__canonical__eqtype_Equality
                                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                    af)) l1) (fun j ->
                              BigBody (j, (fun x1 x2 -> Plus
                              (x1, x2)), true, j))))))
                        (cplus1 af (Obj.magic a1)
                          (Obj.magic a1) l0
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j)))
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j))) (Cid (Obj.magic a1))
                          (Cid
                          (Coq_bigop.body Empt
                            (Obj.magic undup
                              (regex_regex__canonical__eqtype_Equality
                                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                  af)) l1) (fun j -> BigBody
                            (j, (fun x1 x2 -> Plus (x1, x2)),
                            true, j)))))
               | NeqNotEq ->
                 let b1 =
                   in_mem a1
                     (mem
                       (seq_predType
                         (regex_regex__canonical__eqtype_Equality
                           (Finite.Exports.fintype_Finite__to__eqtype_Equality
                             af))) l1)
                 in
                 if b1
                 then ctrans2 af
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun i -> BigBody
                          (i, (fun x1 x2 -> Plus (x1, x2)),
                          true, i))) l0 (Plus
                        ((Coq_bigop.body Empt
                           (Obj.magic undup
                             (regex_regex__canonical__eqtype_Equality
                               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                 af)) l1) (fun i -> BigBody
                           (i, (fun x1 x2 -> Plus (x1, x2)),
                           true, i))), (Obj.magic a2))) (Plus
                        ((Obj.magic a2),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun i -> BigBody
                          (i, (fun x1 x2 -> Plus (x1, x2)),
                          true, i))))) (Retag
                        ((Coq_bigop.body Empt
                           (Obj.magic undup
                             (regex_regex__canonical__eqtype_Equality
                               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                 af)) l1) (fun i -> BigBody
                           (i, (fun x1 x2 -> Plus (x1, x2)),
                           true, i))), (Obj.magic a2))) (TagL
                        ((Coq_bigop.body Empt
                           (Obj.magic undup
                             (regex_regex__canonical__eqtype_Equality
                               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                 af)) l1) (fun i -> BigBody
                           (i, (fun x1 x2 -> Plus (x1, x2)),
                           true, i))), (Obj.magic a2)))
                 else ctrans2 af (Plus ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))) l0 (Plus ((Plus
                        ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))), (Obj.magic a2)))
                        (Plus ((Obj.magic a2), (Plus
                        ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))))) (Retag ((Plus
                        ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))), (Obj.magic a2)))
                        (TagL ((Plus ((Obj.magic a1),
                        (Coq_bigop.body Empt
                          (Obj.magic undup
                            (regex_regex__canonical__eqtype_Equality
                              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                                af)) l1) (fun j -> BigBody
                          (j, (fun x1 x2 -> Plus (x1, x2)),
                          true, j))))), (Obj.magic a2))))
            in
            let rec f l1 a1 =
              match l1 with
              | [] -> _evar_0_0 a1
              | y :: l2 ->
                Obj.magic _evar_0_1 y l2 (fun a2 _ ->
                  f l2 a2) a1
            in f (Obj.magic l) a0)
    else Dsl_fix ((Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))))),
           (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))), (Dsl_fix ((Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))))),
           (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))), (Dsl_fix ((Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))))),
           (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))), (Cplus ((Obj.magic a0), (Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))), (Cid (Obj.magic a0)),
           (x (((Plus ((Obj.magic a0),
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun j -> BigBody (j,
               (fun x0 x1 -> Plus (x0, x1)), true, j))))),
             (Plus ((Obj.magic a0),
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j)))))) :: (((Plus ((Obj.magic a0),
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun j -> BigBody (j,
               (fun x0 x1 -> Plus (x0, x1)), true, j))))),
             (Plus ((Obj.magic a0),
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j)))))) :: (((Plus ((Obj.magic a0),
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun j -> BigBody (j,
               (fun x0 x1 -> Plus (x0, x1)), true, j))))),
             (Plus ((Obj.magic a0),
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j)))))) :: l0)))))))))))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> Obj.magic _evar_0_0 y l0 (f l0)
  in f __top_assumption_

(** val c_eq_undup2 :
    Finite.coq_type -> regex list -> (regex * regex) list ->
    dsl **)

let c_eq_undup2 af __top_assumption_ =
  let _evar_0_ = fun _ -> Cid
    (Coq_bigop.body Empt [] (fun i -> BigBody (i,
      (fun x x0 -> Plus (x, x0)), true, i)))
  in
  let _evar_0_0 = fun a0 l x l0 ->
    let b0 =
      in_mem a0
        (mem
          (seq_predType
            (regex_regex__canonical__eqtype_Equality
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af))) l)
    in
    if b0
    then ctrans2 af (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))) l0
           (Coq_bigop.body Empt (Obj.magic l) (fun i ->
             BigBody (i, (fun x0 x1 -> Plus (x0, x1)), true,
             i)))
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun i -> BigBody (i,
             (fun x0 x1 -> Plus (x0, x1)), true, i))) 
           (x l0)
           (let _evar_0_0 = fun _ -> assert false
              (* absurd case *)
            in
            let _evar_0_1 = fun a1 l1 x0 a2 ->
              let e =
                eqVneq
                  (regex_regex__canonical__eqtype_Equality
                    (Finite.Exports.fintype_Finite__to__eqtype_Equality
                      af)) a2 a1
              in
              (match e with
               | EqNotNeq ->
                 ctrans1 af (Plus ((Obj.magic a1), (Plus
                   ((Obj.magic a1),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j))))))) l0 (Plus ((Plus
                   ((Obj.magic a1), (Obj.magic a1))),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j))))) (Plus ((Obj.magic a1),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j))))) (Shuffleinv ((Obj.magic a1),
                   (Obj.magic a1),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j)))))
                   (cplus1 af (Plus ((Obj.magic a1),
                     (Obj.magic a1))) (Obj.magic a1) l0
                     (Coq_bigop.body Empt l1 (fun j ->
                       BigBody (j, (fun x1 x2 -> Plus (x1,
                       x2)), true, j)))
                     (Coq_bigop.body Empt l1 (fun j ->
                       BigBody (j, (fun x1 x2 -> Plus (x1,
                       x2)), true, j))) (Untag
                     (Obj.magic a1)) (Cid
                     (Coq_bigop.body Empt l1 (fun j ->
                       BigBody (j, (fun x1 x2 -> Plus (x1,
                       x2)), true, j)))))
               | NeqNotEq ->
                 ctrans1 af (Plus ((Obj.magic a2), (Plus
                   ((Obj.magic a1),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j))))))) l0 (Plus ((Plus
                   ((Obj.magic a2), (Obj.magic a1))),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j))))) (Plus ((Obj.magic a1),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j))))) (Shuffleinv ((Obj.magic a2),
                   (Obj.magic a1),
                   (Coq_bigop.body Empt l1 (fun j -> BigBody
                     (j, (fun x1 x2 -> Plus (x1, x2)), true,
                     j)))))
                   (ctrans1 af (Plus ((Plus ((Obj.magic a2),
                     (Obj.magic a1))),
                     (Coq_bigop.body Empt l1 (fun j ->
                       BigBody (j, (fun x1 x2 -> Plus (x1,
                       x2)), true, j))))) l0 (Plus ((Plus
                     ((Obj.magic a1), (Obj.magic a2))),
                     (Coq_bigop.body Empt l1 (fun j ->
                       BigBody (j, (fun x1 x2 -> Plus (x1,
                       x2)), true, j))))) (Plus
                     ((Obj.magic a1),
                     (Coq_bigop.body Empt l1 (fun j ->
                       BigBody (j, (fun x1 x2 -> Plus (x1,
                       x2)), true, j)))))
                     (cplus1 af (Plus ((Obj.magic a2),
                       (Obj.magic a1))) (Plus
                       ((Obj.magic a1), (Obj.magic a2))) l0
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j)))
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j))) (Retag
                       ((Obj.magic a2), (Obj.magic a1))) (Cid
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j)))))
                     (ctrans1 af (Plus ((Plus
                       ((Obj.magic a1), (Obj.magic a2))),
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j))))) l0 (Plus
                       ((Obj.magic a1), (Plus
                       ((Obj.magic a2),
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j))))))) (Plus
                       ((Obj.magic a1),
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j))))) (Shuffle
                       ((Obj.magic a1), (Obj.magic a2),
                       (Coq_bigop.body Empt l1 (fun j ->
                         BigBody (j, (fun x1 x2 -> Plus (x1,
                         x2)), true, j)))))
                       (cplus1 af (Obj.magic a1)
                         (Obj.magic a1) l0 (Plus
                         ((Obj.magic a2),
                         (Coq_bigop.body Empt l1 (fun j ->
                           BigBody (j, (fun x1 x2 -> Plus
                           (x1, x2)), true, j)))))
                         (Coq_bigop.body Empt l1 (fun j ->
                           BigBody (j, (fun x1 x2 -> Plus
                           (x1, x2)), true, j))) (Cid
                         (Obj.magic a1)) (x0 a2 __)))))
            in
            let rec f l1 a1 =
              match l1 with
              | [] -> _evar_0_0 a1
              | y :: l2 ->
                Obj.magic _evar_0_1 y l2 (fun a2 _ ->
                  f l2 a2) a1
            in f (Obj.magic l) a0)
    else Dsl_fix ((Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))), (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))))),
           (Dsl_fix ((Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))), (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))))),
           (Dsl_fix ((Plus ((Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))))), (Plus ((Obj.magic a0),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))))),
           (Cplus ((Obj.magic a0), (Obj.magic a0),
           (Coq_bigop.body Empt (Obj.magic l) (fun j ->
             BigBody (j, (fun x0 x1 -> Plus (x0, x1)), true,
             j))),
           (Coq_bigop.body Empt
             (Obj.magic undup
               (regex_regex__canonical__eqtype_Equality
                 (Finite.Exports.fintype_Finite__to__eqtype_Equality
                   af)) l) (fun j -> BigBody (j,
             (fun x0 x1 -> Plus (x0, x1)), true, j))), (Cid
           (Obj.magic a0)),
           (x (((Plus ((Obj.magic a0),
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j))))), (Plus ((Obj.magic a0),
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun j -> BigBody (j,
               (fun x0 x1 -> Plus (x0, x1)), true, j)))))) :: (((Plus
             ((Obj.magic a0),
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j))))), (Plus ((Obj.magic a0),
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun j -> BigBody (j,
               (fun x0 x1 -> Plus (x0, x1)), true, j)))))) :: (((Plus
             ((Obj.magic a0),
             (Coq_bigop.body Empt (Obj.magic l) (fun j ->
               BigBody (j, (fun x0 x1 -> Plus (x0, x1)),
               true, j))))), (Plus ((Obj.magic a0),
             (Coq_bigop.body Empt
               (Obj.magic undup
                 (regex_regex__canonical__eqtype_Equality
                   (Finite.Exports.fintype_Finite__to__eqtype_Equality
                     af)) l) (fun j -> BigBody (j,
               (fun x0 x1 -> Plus (x0, x1)), true, j)))))) :: l0)))))))))))
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> Obj.magic _evar_0_0 y l0 (f l0)
  in f __top_assumption_

(** val o_o_l : Finite.coq_type -> regex list -> dsl **)

let o_o_l af l =
  Cid
    (if has
          (nu
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af)) l
     then Eps
     else Empt)

(** val o_o_l2 : Finite.coq_type -> pder -> dsl **)

let o_o_l2 af l =
  Cid
    (if has
          (nu
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af)) l
     then Eps
     else Empt)

(** val decomp_p1_aux :
    Finite.coq_type -> regex list -> dsl **)

let decomp_p1_aux af l =
  ctrans1 af
    (Coq_bigop.body Empt l (fun i -> BigBody (i, (fun x x0 ->
      Plus (x, x0)), true, i))) [] (Plus
    ((o
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       (Coq_bigop.body Empt l (fun i -> BigBody (i,
         (fun x x0 -> Plus (x, x0)), true, i)))),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0
        (Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i)))))))))))
    (Plus
    ((o_l
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       l),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i))))))))))
    (derive_unfold_coerce_l af
      (Coq_bigop.body Empt l (fun i -> BigBody (i,
        (fun x x0 -> Plus (x, x0)), true, i)))) (Cplus
    ((o
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       (Coq_bigop.body Empt l (fun i -> BigBody (i,
         (fun x x0 -> Plus (x, x0)), true, i)))),
    (o_l
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      l),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0
        (Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i))))))))),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i)))))))), (o_o_l af l),
    (eq_big_plus_c af (index_enum af) (fun i -> Seq ((Event
      i),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) i
        (Coq_bigop.body Empt l (fun i0 -> BigBody (i0,
          (fun x x0 -> Plus (x, x0)), true, i0))))))
      (fun i -> Seq ((Event i),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) i l) (fun i0 -> BigBody (i0, (fun x x0 ->
        Plus (x, x0)), true, i0))))) [] (fun a0 _ -> Cseq
      ((Event a0), (Event a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0
        (Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i)))),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i))), (Cid (Event a0)),
      (ctrans2 af
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0
          (Coq_bigop.body Empt l (fun i -> BigBody (i,
            (fun x x0 -> Plus (x, x0)), true, i)))) []
        (Coq_bigop.body Empt
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0
            (Coq_bigop.body Empt l (fun i -> BigBody (i,
              (fun x x0 -> Plus (x, x0)), true, i))))
          (fun i -> BigBody (i, (fun x x0 -> Plus (x, x0)),
          true, i)))
        (Coq_bigop.body Empt
          (Obj.magic undup
            (regex_regex__canonical__eqtype_Equality
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af))
            (pd
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0
              (Coq_bigop.body Empt l (fun i -> BigBody (i,
                (fun x x0 -> Plus (x, x0)), true, i)))))
          (fun i -> BigBody (i, (fun x x0 -> Plus (x, x0)),
          true, i)))
        (c_eq_undup2 af
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0
            (Coq_bigop.body Empt l (fun i -> BigBody (i,
              (fun x x0 -> Plus (x, x0)), true, i)))) [])
        (c_eq_derive_pd_l1 af
          (Coq_bigop.body Empt l (fun i -> BigBody (i,
            (fun x x0 -> Plus (x, x0)), true, i))) [] a0)))))))

(** val dsl_mon :
    Finite.coq_type -> (regex * regex) list -> Equality.sort
    list -> regex -> regex -> dsl -> dsl **)

let dsl_mon _ l l' e f p =
  let _evar_0_ = fun _ a0 b0 c _ -> Shuffle (a0, b0, c) in
  let _evar_0_0 = fun _ a0 b0 c _ -> Shuffleinv (a0, b0, c) in
  let _evar_0_1 = fun _ a0 b0 _ -> Retag (a0, b0) in
  let _evar_0_2 = fun _ a0 _ -> UntagL a0 in
  let _evar_0_3 = fun _ a0 _ -> UntagLinv a0 in
  let _evar_0_4 = fun _ a0 _ -> Untag a0 in
  let _evar_0_5 = fun _ a0 b0 _ -> TagL (a0, b0) in
  let _evar_0_6 = fun _ a0 b0 c _ -> Assoc (a0, b0, c) in
  let _evar_0_7 = fun _ a0 b0 c _ -> Associnv (a0, b0, c) in
  let _evar_0_8 = fun _ a0 _ -> Swap a0 in
  let _evar_0_9 = fun _ a0 _ -> Swapinv a0 in
  let _evar_0_10 = fun _ a0 _ -> Proj a0 in
  let _evar_0_11 = fun _ a0 _ -> Projinv a0 in
  let _evar_0_12 = fun _ a0 _ -> AbortR a0 in
  let _evar_0_13 = fun _ a0 _ -> AbortRinv a0 in
  let _evar_0_14 = fun _ a0 _ -> AbortL a0 in
  let _evar_0_15 = fun _ a0 _ -> AbortLinv a0 in
  let _evar_0_16 = fun _ a0 b0 c _ -> DistL (a0, b0, c) in
  let _evar_0_17 = fun _ a0 b0 c _ -> DistLinv (a0, b0, c) in
  let _evar_0_18 = fun _ a0 b0 c _ -> DistR (a0, b0, c) in
  let _evar_0_19 = fun _ a0 b0 c _ -> DistRinv (a0, b0, c) in
  let _evar_0_20 = fun _ a0 _ -> Wrap a0 in
  let _evar_0_21 = fun _ a0 _ -> Wrapinv a0 in
  let _evar_0_22 = fun _ a0 b0 _ x l'0 -> Drop (a0, b0,
    (x l'0 __))
  in
  let _evar_0_23 = fun _ a0 _ -> Cid a0 in
  let _evar_0_24 = fun _ a0 b0 c _ x _ x0 l'0 -> Ctrans (a0,
    a0, c, (Cid a0), (Ctrans (a0, a0, c, (Cid a0), (Ctrans
    (a0, b0, c, (x l'0 __), (x0 l'0 __))))))
  in
  let _evar_0_25 = fun _ a0 a' b0 b' _ x _ x0 l'0 -> Cplus
    (a0, a', b0, b', (x l'0 __), (x0 l'0 __))
  in
  let _evar_0_26 = fun _ a0 a' b0 b' _ x _ x0 l'0 -> Cseq
    (a0, a', b0, b', (x l'0 __), (x0 l'0 __))
  in
  let _evar_0_27 = fun _ a0 a1 b0 _ -> Dsl_var (a0, a1, b0) in
  let _evar_0_28 = fun _ a0 b0 _ x l'0 -> Dsl_fix (a0, b0,
    (x ((a0, b0) :: l'0) __))
  in
  let rec f0 r _ _ d l'0 =
    match d with
    | Shuffle (a0, b0, c) -> _evar_0_ r a0 b0 c l'0
    | Shuffleinv (a0, b0, c) -> _evar_0_0 r a0 b0 c l'0
    | Retag (a0, b0) -> _evar_0_1 r a0 b0 l'0
    | UntagL a0 -> _evar_0_2 r a0 l'0
    | UntagLinv a0 -> _evar_0_3 r a0 l'0
    | Untag a0 -> _evar_0_4 r a0 l'0
    | TagL (a0, b0) -> _evar_0_5 r a0 b0 l'0
    | Assoc (a0, b0, c) -> _evar_0_6 r a0 b0 c l'0
    | Associnv (a0, b0, c) -> _evar_0_7 r a0 b0 c l'0
    | Swap a0 -> _evar_0_8 r a0 l'0
    | Swapinv a0 -> _evar_0_9 r a0 l'0
    | Proj a0 -> _evar_0_10 r a0 l'0
    | Projinv a0 -> _evar_0_11 r a0 l'0
    | AbortR a0 -> _evar_0_12 r a0 l'0
    | AbortRinv a0 -> _evar_0_13 r a0 l'0
    | AbortL a0 -> _evar_0_14 r a0 l'0
    | AbortLinv a0 -> _evar_0_15 r a0 l'0
    | DistL (a0, b0, c) -> _evar_0_16 r a0 b0 c l'0
    | DistLinv (a0, b0, c) -> _evar_0_17 r a0 b0 c l'0
    | DistR (a0, b0, c) -> _evar_0_18 r a0 b0 c l'0
    | DistRinv (a0, b0, c) -> _evar_0_19 r a0 b0 c l'0
    | Wrap a0 -> _evar_0_20 r a0 l'0
    | Wrapinv a0 -> _evar_0_21 r a0 l'0
    | Drop (a0, b0, d0) ->
      _evar_0_22 r a0 b0 d0 (fun l'1 _ ->
        f0 r a0 (Plus (Eps, b0)) d0 l'1) l'0
    | Cid a0 -> _evar_0_23 r a0 l'0
    | Ctrans (a0, b0, c, d0, d1) ->
      _evar_0_24 r a0 b0 c d0 (fun l'1 _ ->
        f0 r a0 b0 d0 l'1) d1 (fun l'1 _ -> f0 r b0 c d1 l'1)
        l'0
    | Cplus (a0, a', b0, b', d0, d1) ->
      _evar_0_25 r a0 a' b0 b' d0 (fun l'1 _ ->
        f0 r a0 a' d0 l'1) d1 (fun l'1 _ ->
        f0 r b0 b' d1 l'1) l'0
    | Cseq (a0, a', b0, b', d0, d1) ->
      _evar_0_26 r a0 a' b0 b' d0 (fun l'1 _ ->
        f0 r a0 a' d0 l'1) d1 (fun l'1 _ ->
        f0 r b0 b' d1 l'1) l'0
    | Dsl_var (a0, a1, b0) -> _evar_0_27 r a0 a1 b0 l'0
    | Dsl_fix (a0, b0, d0) ->
      Obj.magic _evar_0_28 r a0 b0 d0 (fun l'1 _ ->
        f0 ((a0, b0) :: r) a0 b0 d0 l'1) l'0
  in f0 l e f p l'

(** val decomp_p1 :
    Finite.coq_type -> regex list -> (regex * regex) list ->
    dsl **)

let decomp_p1 af l l0 =
  let _evar_0_ = [] in
  let _evar_0_0 = decomp_p1_aux af l in
  dsl_mon af _evar_0_ (Obj.magic l0)
    (Coq_bigop.body Empt l (fun i -> BigBody (i, (fun x x0 ->
      Plus (x, x0)), true, i))) (Plus
    ((o_l
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       l),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i)))))))))) _evar_0_0

(** val decomp_p2_aux : Finite.coq_type -> pder -> dsl **)

let decomp_p2_aux af l =
  ctrans2 af (Plus
    ((o_l
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       l),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i)))))))))) [] (Plus
    ((o
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       (Coq_bigop.body Empt l (fun i -> BigBody (i,
         (fun x x0 -> Plus (x, x0)), true, i)))),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0
        (Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i)))))))))))
    (Coq_bigop.body Empt l (fun i -> BigBody (i, (fun x x0 ->
      Plus (x, x0)), true, i)))
    (derive_unfold_coerce_r af
      (Coq_bigop.body Empt l (fun i -> BigBody (i,
        (fun x x0 -> Plus (x, x0)), true, i)))) (Cplus
    ((o_l
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       l),
    (o
      (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
      (Coq_bigop.body Empt l (fun i -> BigBody (i,
        (fun x x0 -> Plus (x, x0)), true, i)))),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i)))))))),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0
        (Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i))))))))),
    (o_o_l2 af l),
    (eq_big_plus_c af (index_enum af) (fun i -> Seq ((Event
      i),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) i l) (fun i0 -> BigBody (i0, (fun x x0 ->
        Plus (x, x0)), true, i0))))) (fun i -> Seq ((Event
      i),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) i
        (Coq_bigop.body Empt l (fun i0 -> BigBody (i0,
          (fun x x0 -> Plus (x, x0)), true, i0)))))) []
      (fun a0 _ -> Cseq ((Event a0), (Event a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i))),
      (derive
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af) a0
        (Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i)))), (Cid
      (Event a0)),
      (ctrans1 af
        (Coq_bigop.body Empt
          (Obj.magic undup
            (regex_regex__canonical__eqtype_Equality
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af))
            (pd
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af) a0
              (Coq_bigop.body Empt l (fun i -> BigBody (i,
                (fun x x0 -> Plus (x, x0)), true, i)))))
          (fun i -> BigBody (i, (fun x x0 -> Plus (x, x0)),
          true, i))) []
        (Coq_bigop.body Empt
          (pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0
            (Coq_bigop.body Empt l (fun i -> BigBody (i,
              (fun x x0 -> Plus (x, x0)), true, i))))
          (fun i -> BigBody (i, (fun x x0 -> Plus (x, x0)),
          true, i)))
        (derive
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0
          (Coq_bigop.body Empt l (fun i -> BigBody (i,
            (fun x x0 -> Plus (x, x0)), true, i))))
        (c_eq_undup1 af
          (Obj.magic pd
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) a0
            (Coq_bigop.body Empt l (fun i -> BigBody (i,
              (fun x x0 -> Plus (x, x0)), true, i)))) [])
        (c_eq_derive_pd_l2 af
          (Coq_bigop.body Empt l (fun i -> BigBody (i,
            (fun x x0 -> Plus (x, x0)), true, i))) [] a0)))))))

(** val decomp_p2 :
    Finite.coq_type -> pder -> (regex * regex) list -> dsl **)

let decomp_p2 af l l0 =
  let _evar_0_ = [] in
  let _evar_0_0 = decomp_p2_aux af l in
  dsl_mon af _evar_0_ (Obj.magic l0) (Plus
    ((o_l
       (Finite.Exports.fintype_Finite__to__eqtype_Equality af)
       l),
    (Coq_bigop.body Empt (index_enum af) (fun a0 -> BigBody
      (a0, (fun x x0 -> Plus (x, x0)), true, (Seq ((Event
      a0),
      (Coq_bigop.body Empt
        (Obj.magic pd_l
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af) a0 l) (fun i -> BigBody (i, (fun x x0 -> Plus
        (x, x0)), true, i))))))))))
    (Coq_bigop.body Empt l (fun i -> BigBody (i, (fun x x0 ->
      Plus (x, x0)), true, i))) _evar_0_0

(** val check_o : Finite.coq_type -> pder -> pder -> bool **)

let check_o af l0 l1 =
  implb
    (has
      (nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af)) l0)
    (has
      (nu
        (Finite.Exports.fintype_Finite__to__eqtype_Equality
          af)) l1)

type ('a, 'b) sumboolT =
| LeftT of 'a
| RightT of 'b

(** val eQ_complete_aux :
    Finite.coq_type -> nType -> (pder * pder) list ->
    (regex * regex) list -> (__, dsl) sumboolT **)

let rec eQ_complete_aux af p v l =
  let b0 =
    in_mem (Obj.magic p)
      (mem
        (seq_predType
          (datatypes_prod__canonical__eqtype_Equality
            (datatypes_list__canonical__eqtype_Equality
              (regex_regex__canonical__eqtype_Equality
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af)))
            (datatypes_list__canonical__eqtype_Equality
              (regex_regex__canonical__eqtype_Equality
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af))))) (Obj.magic v))
  in
  if b0
  then LeftT __
  else RightT (Dsl_fix
         ((Coq_bigop.body Empt (fst p) (fun i -> BigBody (i,
            (fun x x0 -> Plus (x, x0)), true, i))),
         (Coq_bigop.body Empt (snd p) (fun i -> BigBody (i,
           (fun x x0 -> Plus (x, x0)), true, i))), (Ctrans
         ((Coq_bigop.body Empt (fst p) (fun i -> BigBody (i,
            (fun x x0 -> Plus (x, x0)), true, i))), (Plus
         ((o_l
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (fst p)),
         (Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (Coq_bigop.body Empt
             (Obj.magic pd_l
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 (fst p)) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))))))))),
         (Coq_bigop.body Empt (snd p) (fun i -> BigBody (i,
           (fun x x0 -> Plus (x, x0)), true, i))),
         (decomp_p1 af (fst p)
           (((Coq_bigop.body Empt (fst p) (fun i -> BigBody
               (i, (fun x x0 -> Plus (x, x0)), true, i))),
           (Coq_bigop.body Empt (snd p) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))) :: l)),
         (Ctrans ((Plus
         ((o_l
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (fst p)),
         (Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (Coq_bigop.body Empt
             (Obj.magic pd_l
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 (fst p)) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))))))))),
         (Plus
         ((o_l
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (snd p)),
         (Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (Coq_bigop.body Empt
             (Obj.magic pd_l
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 (snd p)) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))))))))),
         (Coq_bigop.body Empt (snd p) (fun i -> BigBody (i,
           (fun x x0 -> Plus (x, x0)), true, i))), (Cplus
         ((o_l
            (Finite.Exports.fintype_Finite__to__eqtype_Equality
              af) (fst p)),
         (o_l
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af) (snd p)),
         (Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (Coq_bigop.body Empt
             (Obj.magic pd_l
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 (fst p)) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))))))),
         (Coq_bigop.body Empt (index_enum af) (fun a0 ->
           BigBody (a0, (fun x x0 -> Plus (x, x0)), true,
           (Seq ((Event a0),
           (Coq_bigop.body Empt
             (Obj.magic pd_l
               (Finite.Exports.fintype_Finite__to__eqtype_Equality
                 af) a0 (snd p)) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))))))),
         (dsl_mon af []
           ((Obj.magic
              ((Coq_bigop.body Empt (fst p) (fun i -> BigBody
                 (i, (fun x x0 -> Plus (x, x0)), true, i))),
              (Coq_bigop.body Empt (snd p) (fun i -> BigBody
                (i, (fun x x0 -> Plus (x, x0)), true, i))))) :: 
           (Obj.magic l))
           (o_l
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) (fst p))
           (o_l
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af) (snd p)) (o_lP af (fst p) (snd p) [])),
         (let (a0, b1) = p in
          let x = fun a1 ->
            let r0 =
              Coq_bigop.body Empt
                (Obj.magic pd_l
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a1 a0) (fun i -> BigBody (i,
                (fun x x0 -> Plus (x, x0)), true, i))
            in
            let r1 =
              Coq_bigop.body Empt
                (Obj.magic pd_l
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) a1 b1) (fun i -> BigBody (i,
                (fun x x0 -> Plus (x, x0)), true, i))
            in
            let x =
              Obj.magic eQ_complete_aux af
                (Obj.magic pair_pd_l af a1 (a0, b1)) ((a0,
                b1) :: v)
                (((Coq_bigop.body Empt a0 (fun i -> BigBody
                    (i, (fun x x0 -> Plus (x, x0)), true, i))),
                (Coq_bigop.body Empt b1 (fun i -> BigBody (i,
                  (fun x x0 -> Plus (x, x0)), true, i)))) :: l)
            in
            (match x with
             | LeftT _ ->
               Dsl_var (a1, (Obj.magic r0), (Obj.magic r1))
             | RightT b2 ->
               Cseq ((Event a1), (Event a1), r0, r1, (Cid
                 (Event a1)), b2))
          in
          let lA = index_enum af in
          let _evar_0_ = fun _ -> Cid Empt in
          let _evar_0_0 = fun a1 l0 x0 x1 -> Cplus ((Seq
            ((Event a1),
            (Coq_bigop.body Empt
              (Obj.magic pd_l
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a1 a0) (fun i -> BigBody (i,
              (fun x2 x3 -> Plus (x2, x3)), true, i))))),
            (Seq ((Event a1),
            (Coq_bigop.body Empt
              (Obj.magic pd_l
                (Finite.Exports.fintype_Finite__to__eqtype_Equality
                  af) a1 b1) (fun i -> BigBody (i,
              (fun x2 x3 -> Plus (x2, x3)), true, i))))),
            (Coq_bigop.body Empt l0 (fun j -> BigBody (j,
              (fun x2 x3 -> Plus (x2, x3)), true, (Seq
              ((Event j),
              (Coq_bigop.body Empt
                (Obj.magic pd_l
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) j a0) (fun i -> BigBody (i,
                (fun x2 x3 -> Plus (x2, x3)), true, i)))))))),
            (Coq_bigop.body Empt l0 (fun j -> BigBody (j,
              (fun x2 x3 -> Plus (x2, x3)), true, (Seq
              ((Event j),
              (Coq_bigop.body Empt
                (Obj.magic pd_l
                  (Finite.Exports.fintype_Finite__to__eqtype_Equality
                    af) j b1) (fun i -> BigBody (i,
                (fun x2 x3 -> Plus (x2, x3)), true, i)))))))),
            (x1 a1), (x0 x1))
          in
          let rec f = function
          | [] -> _evar_0_
          | y :: l1 -> _evar_0_0 y l1 (f l1)
          in f lA x))),
         (decomp_p2 af (snd p)
           (((Coq_bigop.body Empt (fst p) (fun i -> BigBody
               (i, (fun x x0 -> Plus (x, x0)), true, i))),
           (Coq_bigop.body Empt (snd p) (fun i -> BigBody (i,
             (fun x x0 -> Plus (x, x0)), true, i)))) :: l))))))))

(** val bisim_c_eq :
    Finite.coq_type -> pder -> pder -> dsl **)

let bisim_c_eq af l l' =
  let h =
    eQ_complete_aux af
      ((Obj.magic undup
         (regex_regex__canonical__eqtype_Equality
           (Finite.Exports.fintype_Finite__to__eqtype_Equality
             af)) l),
      (Obj.magic undup
        (regex_regex__canonical__eqtype_Equality
          (Finite.Exports.fintype_Finite__to__eqtype_Equality
            af)) l')) [] []
  in
  (match h with
   | LeftT _ -> assert false (* absurd case *)
   | RightT b0 ->
     Ctrans
       ((Coq_bigop.body Empt l (fun i -> BigBody (i,
          (fun x x0 -> Plus (x, x0)), true, i))),
       (Coq_bigop.body Empt
         (Obj.magic undup
           (regex_regex__canonical__eqtype_Equality
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af)) l) (fun i -> BigBody (i, (fun x x0 ->
         Plus (x, x0)), true, i))),
       (Coq_bigop.body Empt l' (fun i -> BigBody (i,
         (fun x x0 -> Plus (x, x0)), true, i))),
       (c_eq_undup2 af l []), (Ctrans
       ((Coq_bigop.body Empt
          (Obj.magic undup
            (regex_regex__canonical__eqtype_Equality
              (Finite.Exports.fintype_Finite__to__eqtype_Equality
                af)) l) (fun i -> BigBody (i, (fun x x0 ->
          Plus (x, x0)), true, i))),
       (Coq_bigop.body Empt
         (Obj.magic undup
           (regex_regex__canonical__eqtype_Equality
             (Finite.Exports.fintype_Finite__to__eqtype_Equality
               af)) l') (fun i -> BigBody (i, (fun x x0 ->
         Plus (x, x0)), true, i))),
       (Coq_bigop.body Empt l' (fun i -> BigBody (i,
         (fun x x0 -> Plus (x, x0)), true, i))), b0,
       (c_eq_undup1 af (Obj.magic l') [])))))

(** val c_eq_completeness :
    Finite.coq_type -> regex -> regex -> dsl **)

let c_eq_completeness af c0 c1 =
  let _view_subject_ = bisim_c_eq af (c0 :: []) (c1 :: []) in
  Ctrans (c0, c0, c1, (Cid c0), (Ctrans (c0, (Plus (c0,
  Empt)), c1, (TagL (c0, Empt)), (Ctrans ((Plus (c0, Empt)),
  (Plus (c1, Empt)), c1, _view_subject_, (Ctrans ((Plus (c1,
  Empt)), (Plus (Empt, c1)), c1, (Retag (c1, Empt)), (UntagL
  c1))))))))

(** val synth_coercion :
    Finite.coq_type -> regex -> regex -> dsl option **)

let synth_coercion af r0 r1 =
  let b0 =
    reachable_wrap af (r0 :: []) (r1 :: []) (check_o af)
  in
  if b0 then Some (c_eq_completeness af r0 r1) else None

type myFin = ordinal

(** val synth_coercion_wrap : regex -> regex -> dsl option **)

let synth_coercion_wrap =
  synth_coercion
    (fintype_ordinal__canonical__fintype_Finite
      (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val inc_seq : int -> int list -> int list **)

let rec inc_seq n0 = function
| [] -> []
| a0 :: l' ->
  if leq (Stdlib.Int.succ (Stdlib.Int.succ a0)) n0
  then (Stdlib.Int.succ a0) :: l'
  else 0 :: (inc_seq n0 l')

(** val to_string :
    'a1 -> 'a1 list -> int list -> 'a1 list **)

let to_string a0 aa l =
  map (nth a0 aa) l

(** val quick_parse_aux :
    int -> myFin list -> regex -> (myFin list * pTree) option **)

let rec quick_parse_aux n0 l r =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match r with
    | Eps ->
      if eq_op0
           (datatypes_list__canonical__eqtype_Equality
             (fintype_ordinal__canonical__eqtype_Equality
               (Stdlib.Int.succ (Stdlib.Int.succ 0))))
           (Obj.magic l) (Obj.magic [])
      then Some ([], P_tt)
      else None
    | Empt -> None
    | Event s ->
      (match l with
       | [] -> None
       | x :: l' ->
         if eq_op0
              (fintype_ordinal__canonical__eqtype_Equality
                (Stdlib.Int.succ (Stdlib.Int.succ 0)))
              (Obj.magic x) s
         then Some (l', (P_singl s))
         else None)
    | Plus (r0, r1) ->
      (match quick_parse_aux n' l r0 with
       | Some p ->
         let (l', t) = p in Some (l', (P_inl (r0, r1, t)))
       | None ->
         (match quick_parse_aux n' l r1 with
          | Some p ->
            let (l', t) = p in Some (l', (P_inr (r0, r1, t)))
          | None -> None))
    | Seq (r0, r1) ->
      (match quick_parse_aux n' l r0 with
       | Some p ->
         let (l', t) = p in
         (match quick_parse_aux n' l' r1 with
          | Some p0 ->
            let (l'', t') = p0 in
            Some (l'', (P_pair (r0, r1, t, t')))
          | None -> None)
       | None -> None)
    | Star r0 ->
      let o0 =
        quick_parse_aux n' l (Plus (Eps, (Seq (r0, (Star
          r0)))))
      in
      (match o0 with
       | Some a0 ->
         let (a1, b0) = a0 in
         pTree_case
           (fintype_ordinal__canonical__eqtype_Equality
             (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Plus
           (Eps, (Seq (r0, (Star r0))))) (fun _ ->
           assert false (* absurd case *)) (fun _ _ ->
           assert false (* absurd case *)) (fun _ _ _ p ->
           Some (a1, (P_fold (r0, (P_inl (Eps, (Seq (r0,
           (Star r0))), p)))))) (fun _ _ _ p ->
           pTree_case
             (fintype_ordinal__canonical__eqtype_Equality
               (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Seq
             (r0, (Star r0))) (fun _ -> assert false
             (* absurd case *)) (fun _ _ -> assert false
             (* absurd case *)) (fun _ _ _ _ -> assert false
             (* absurd case *)) (fun _ _ _ _ -> assert false
             (* absurd case *)) (fun _ _ _ p0 p1 -> Some (a1,
             (P_fold (r0, (P_inr (Eps, (Seq (r0, (Star r0))),
             (P_pair (r0, (Star r0), p0, p1))))))))
             (fun _ _ _ -> assert false (* absurd case *)) p)
           (fun _ _ _ _ _ -> assert false (* absurd case *))
           (fun _ _ _ -> assert false (* absurd case *)) b0
       | None -> None))
    n0

(** val quick_parse :
    int -> myFin list -> regex -> pTree option **)

let quick_parse n0 l r =
  match quick_parse_aux n0 l r with
  | Some p ->
    let (l0, t) = p in
    (match l0 with
     | [] -> Some t
     | _ :: _ -> None)
  | None -> None

(** val parse_inc :
    int -> regex -> int list -> (int list, pTree) sum **)

let parse_inc n0 r l =
  match quick_parse n0
          (to_string (ord0 (Stdlib.Int.succ 0))
            (Obj.magic index_enum
              (fintype_ordinal__canonical__fintype_Finite
                (Stdlib.Int.succ (Stdlib.Int.succ 0)))) l) r with
  | Some t -> Inr t
  | None ->
    Inl
      (inc_seq
        (size
          (index_enum
            (fintype_ordinal__canonical__fintype_Finite
              (Stdlib.Int.succ (Stdlib.Int.succ 0))))) l)

(** val rep_try_parse :
    int -> int -> regex -> int list -> pTree option **)

let rec rep_try_parse n0 n2 r l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match parse_inc n2 r l with
    | Inl l' ->
      if eq_op0
           (datatypes_list__canonical__eqtype_Equality
             datatypes_nat__canonical__eqtype_Equality)
           (Obj.magic l) (Obj.magic l')
      then None
      else rep_try_parse n' n2 r l'
    | Inr t -> Some t)
    n0

(** val my_parse : int -> int -> regex -> pTree option **)

let my_parse fuel size0 r =
  rep_try_parse fuel fuel r (nseq size0 0)

(** val interp_wrap :
    regex -> regex -> dsl -> pTree -> post **)

let interp_wrap r0 r1 d t =
  interp
    (fintype_ordinal__canonical__fintype_Finite
      (Stdlib.Int.succ (Stdlib.Int.succ 0))) [] r0 r1 d t
    (fun _ _ _ _ _ -> assert false (* absurd case *))

(** val dsl_size :
    (regex * regex) list -> regex -> regex -> dsl -> int **)

let rec dsl_size l _ _ = function
| Ctrans (a0, b0, c, d0, d1) ->
  addn (dsl_size l a0 b0 d0) (dsl_size l b0 c d1)
| Cplus (a0, a', b0, b', d0, d1) ->
  addn (dsl_size l a0 a' d0) (dsl_size l b0 b' d1)
| Cseq (a0, a', b0, b', d0, d1) ->
  addn (dsl_size l a0 a' d0) (dsl_size l b0 b' d1)
| Dsl_fix (a0, b0, d0) -> dsl_size ((a0, b0) :: l) a0 b0 d0
| _ -> Stdlib.Int.succ 0

(** val time_synth_coercion : regex -> regex -> dsl option **)

let time_synth_coercion =
  fun x y-> 
  let t = Sys.time() in 
  let fx = synth_coercion_wrap x y in
  Printf.printf "Synthesis time: %fs\n" (Sys.time() -. t);
    fx

(** val time_interp_wrap :
    regex -> regex -> dsl -> pTree -> post **)

let time_interp_wrap =
  fun x y z q -> 
  let t = Sys.time() in 
  let fx = interp_wrap x y z q in 
  Printf.printf "Interpetation time: %fs\n" (Sys.time() -. t);
  fx


(** val interp_size :
    regex -> regex -> dsl -> pTree -> int * pTree **)

let interp_size r0 r1 prog t0 =
let s0 = (pTree_1size
     (fintype_ordinal__canonical__eqtype_Equality
       (Stdlib.Int.succ (Stdlib.Int.succ 0)))
     r0 t0)
  
 in  Printf.printf "String length: %d\n" s0; 
    (s0,time_interp_wrap r0 r1 prog t0)

(** val synth_interp : int -> int list -> regex -> regex -> (int * (int * pTree) list) option **)

let synth_interp n0 l r0 r1 =
  match time_synth_coercion r0 r1 with
  | Some prog ->
    let ts =
      pmap (fun x -> my_parse n0 x r0) l
    in
    if negb
         (eq_op0
           datatypes_nat__canonical__eqtype_Equality
           (Obj.magic size ts)
           (Obj.magic size l))
    then None
    else let n = (dsl_size [] r0 r1 prog) in 
Printf.printf "Coercion size: %d\n" n;
 Some (n, (map (interp_size r0 r1 prog) ts))
  | None -> None


(** val big_nat : int **)

let big_nat =
  of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 (D0 (D0
    Nil))))))))

(** val tree_sizes : int list **)

let tree_sizes =
  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))) :: []))

(** val synth_interp_applied :
    regex -> regex -> (int * (int * pTree) list) option **)

let synth_interp_applied =
  synth_interp big_nat tree_sizes

type re_pair = char list * (regex * regex)

(** val eval_test :
    re_pair -> (int * (int * pTree) list) option **)

let string_of_chars chars = 
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let eval_test rp =
Printf.printf "Testcase: %s\n" (string_of_chars (fst rp));
  synth_interp_applied (fst (snd rp))
    (snd (snd rp))


(** val a : regex **)

let a =
  Event (Obj.magic ord0 (Stdlib.Int.succ 0))

(** val b : regex **)

let b =
  Event (Obj.magic (Stdlib.Int.succ 0))

(** val star_a : regex **)

let star_a =
  Star a

(** val star_star_a : regex **)

let star_star_a =
  Star star_a

(** val rp1 : char list * (regex * regex) **)

let rp1 =
  (('a'::('^'::('*'::(' '::('x'::(' '::('('::('a'::('^'::('*'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::[])))))))))))))))))))),
    ((Seq (star_a, star_star_a)), star_a))

(** val rp1' : char list * (regex * regex) **)

let rp1' =
  (('a'::(' '::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::(' '::('x'::(' '::('('::('a'::('^'::('*'::(')'::('^'::('*'::[]))))))))))))))))))))),
    (star_a, (Seq (star_a, star_star_a))))

(** val rp2 : char list * (regex * regex) **)

let rp2 =
  (('('::('a'::('^'::('*'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::[])))))))))))))),
    (star_star_a, star_a))

(** val rp2' : char list * (regex * regex) **)

let rp2' =
  ((' '::('a'::('^'::('*'::(' '::('<'::('='::(' '::('('::('a'::('^'::('*'::(')'::('^'::('*'::[]))))))))))))))),
    (star_a, star_star_a))

(** val rp3 : char list * (regex * regex) **)

let rp3 =
  (('('::('1'::(' '::('+'::(' '::('a'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::[])))))))))))))))),
    ((Star (Plus (Eps, a))), star_a))

(** val rp3' : char list * (regex * regex) **)

let rp3' =
  (('a'::('^'::('*'::(' '::('<'::('='::(' '::('('::('1'::(' '::('+'::(' '::('a'::(')'::('^'::('*'::[])))))))))))))))),
    (star_a, (Star (Plus (Eps, a)))))

(** val rp4 : char list * (regex * regex) **)

let rp4 =
  (('('::('a'::('+'::('b'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::(' '::('+'::(' '::('('::('b'::('^'::('*'::(' '::('x'::(' '::('a'::('^'::('*'::(')'::('^'::('*'::[])))))))))))))))))))))))))))))),
    ((Star (Plus (a, b))), (Plus ((Star a), (Star (Seq ((Star
    b), (Star a))))))))

(** val rp4' : char list * (regex * regex) **)

let rp4' =
  (('a'::('^'::('*'::(' '::('+'::(' '::('('::('b'::('^'::('*'::(' '::('x'::(' '::('a'::('^'::('*'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('('::('a'::(' '::('+'::(' '::('b'::(')'::('^'::('*'::[])))))))))))))))))))))))))))))))),
    ((Plus ((Star a), (Star (Seq (b, (Star a)))))), (Star
    (Plus (a, b)))))

(** val rp5 : char list * (regex * regex) **)

let rp5 =
  (('a'::('^'::('*'::(' '::('x'::(' '::('b'::('^'::('*'::(' '::('<'::('='::(' '::('('::('('::('1'::(' '::('+'::(' '::('a'::(')'::(' '::('x'::(' '::('('::('1'::(' '::('+'::(' '::('b'::(')'::(')'::('^'::('*'::[])))))))))))))))))))))))))))))))))),
    ((Seq ((Star a), (Star b))), (Star (Seq ((Plus (Eps, a)),
    (Plus (Eps, b)))))))

(** val rp5' : char list * (regex * regex) **)

let rp5' =
  (('('::('('::('1'::(' '::('+'::(' '::('a'::(')'::(' '::('x'::(' '::('('::('1'::(' '::('+'::(' '::('b'::(')'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::(' '::('x'::(' '::('b'::('^'::('*'::(' '::(' '::[])))))))))))))))))))))))))))))))))))),
    ((Seq ((Star (Plus (Eps, a))), (Plus (Eps, b)))), (Seq
    ((Star a), (Star b)))))

(** val rp6 : char list * (regex * regex) **)

let rp6 =
  (('a'::('^'::('*'::(' '::('x'::(' '::('('::('1'::(' '::('+'::(' '::('a'::(')'::(' '::('<'::('='::(' '::('a'::('^'::('*'::[])))))))))))))))))))),
    ((Seq ((Star a), (Plus (Eps, a)))), (Star a)))

(** val rp6' : char list * (regex * regex) **)

let rp6' =
  (('a'::('^'::('*'::(' '::('<'::('='::(' '::('a'::('^'::('*'::(' '::('x'::(' '::('('::('1'::(' '::('+'::(' '::('a'::(')'::[])))))))))))))))))))),
    ((Star a), (Seq ((Star a), (Plus (Eps, a))))))

(** val rp7 : char list * (regex * regex) **)

let rp7 =
  (('('::('a'::(' '::('+'::(' '::('b'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('('::('a'::('^'::('*'::(' '::('+'::(' '::('b'::('^'::('*'::(')'::('^'::('*'::[])))))))))))))))))))))))))),
    ((Star (Plus (a, b))), (Star (Plus ((Star a), (Star
    b))))))

(** val rp7' : char list * (regex * regex) **)

let rp7' =
  (('('::('a'::('^'::('*'::(' '::('+'::(' '::('b'::('^'::('*'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('('::('a'::(' '::('+'::(' '::('b'::(')'::('^'::('*'::[])))))))))))))))))))))))))),
    ((Star (Plus ((Star a), (Star b)))), (Star (Plus (a,
    b)))))

(** val rp8 : char list * (regex * regex) **)

let rp8 =
  (('('::('a'::('^'::('*'::(' '::('+'::(' '::('b'::('^'::('*'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('('::('a'::('^'::('*'::(' '::('x'::(' '::('b'::('^'::('*'::(')'::('^'::('*'::[])))))))))))))))))))))))))))))),
    ((Star (Plus ((Star a), (Star b)))), (Star (Seq ((Star
    a), (Star b))))))

(** val rp8' : char list * (regex * regex) **)

let rp8' =
  (('('::('a'::('^'::('*'::(' '::('x'::(' '::('b'::('^'::('*'::(')'::('^'::('*'::(' '::('<'::('='::(' '::('('::('a'::('^'::('*'::(' '::('+'::(' '::('b'::('^'::('*'::(')'::('^'::('*'::[])))))))))))))))))))))))))))))),
    ((Star (Seq ((Star a), (Star b)))), (Star (Plus ((Star
    a), (Star b))))))

(** val make_test :
    re_pair -> unit -> (int * (int * pTree) list) option **)

let make_test rp _ =
  eval_test rp

(** val test1 : unit -> (int * (int * pTree) list) option **)

let test1 =
  make_test rp1

(** val test1' : unit -> (int * (int * pTree) list) option **)

let test1' =
  make_test rp1'

(** val test2 : unit -> (int * (int * pTree) list) option **)

let test2 =
  make_test rp2

(** val test2' : unit -> (int * (int * pTree) list) option **)

let test2' =
  make_test rp2'

(** val test3 : unit -> (int * (int * pTree) list) option **)

let test3 =
  make_test rp3

(** val test3' : unit -> (int * (int * pTree) list) option **)

let test3' =
  make_test rp3'

(** val test4 : unit -> (int * (int * pTree) list) option **)

let test4 =
  make_test rp4

(** val test4' : unit -> (int * (int * pTree) list) option **)

let test4' =
  make_test rp4'

(** val test5 : unit -> (int * (int * pTree) list) option **)

let test5 =
  make_test rp5

(** val test5' : unit -> (int * (int * pTree) list) option **)

let test5' =
  make_test rp5'

(** val test6 : unit -> (int * (int * pTree) list) option **)

let test6 =
  make_test rp6

(** val test6' : unit -> (int * (int * pTree) list) option **)

let test6' =
  make_test rp6'

(** val test7 : unit -> (int * (int * pTree) list) option **)

let test7 =
  make_test rp7

(** val test7' : unit -> (int * (int * pTree) list) option **)

let test7' =
  make_test rp7'

(** val test8 : unit -> (int * (int * pTree) list) option **)

let test8 =
  make_test rp8

(** val test8' : unit -> (int * (int * pTree) list) option **)

let test8' =
  make_test rp8'

(** val test :
    (((((((((((((((unit -> (int * (int * pTree) list)
    option) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list)
    option)) * (unit -> (int * (int * pTree) list) option) **)

let test =
  (((((((((((((((test1, test1'), test2), test2'), test3),
    test3'), test4), test4'), test5), test5'), test6),
    test6'), test7), test7'), test8), test8')
