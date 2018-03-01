chapter \<open>Generated by Lem from basic_classes.lem.\<close>

theory "Lem_basic_classes" 

imports 
 	 Main
	 "Lem_bool" 
	 "HOL-Library.Datatype_Records" 

begin 

(******************************************************************************)
(* Basic Type Classes                                                         *)
(******************************************************************************)

(*open import Bool*) 
(*open import {isabelle} `HOL-Library.Datatype_Records`*)

(*open import {coq} `Coq.Strings.Ascii`*)

(* ========================================================================== *)
(* Equality                                                                   *)
(* ========================================================================== *)

(* Lem`s default equality (=) is defined by the following type-class Eq.
   This typeclass should define equality on an abstract datatype 'a. It should
   always coincide with the default equality of Coq, HOL and Isabelle.
   For OCaml, it might be different, since abstract datatypes like sets
   might have fancy equalities. *)

(*class ( Eq 'a ) 
  val = [isEqual] : 'a -> 'a -> bool
  val <> [isInequal] : 'a -> 'a -> bool
end*)


(* (=) should for all instances be an equivalence relation 
   The isEquivalence predicate of relations could be used here.
   However, this would lead to a cyclic dependency. *)

(* TODO: add later, once lemmata can be assigned to classes 
lemma eq_equiv: ((forall x. (x = x)) &&
                 (forall x y. (x = y) <-> (y = x)) &&
                 (forall x y z. ((x = y) && (y = z)) --> (x = z)))
*)

(* Structural equality *)

(* Sometimes, it is also handy to be able to use structural equality.
   This equality is mapped to the build-in equality of backends. This equality
   differs significantly for each backend. For example, OCaml can`t check equality
   of function types, whereas HOL can.  When using structural equality, one should 
   know what one is doing. The only guarentee is that is behaves like 
   the native backend equality.

   A lengthy name for structural equality is used to discourage its direct use.
   It also ensures that users realise it is unsafe (e.g. OCaml can`t check two functions
   for equality *)
(*val unsafe_structural_equality : forall 'a. 'a -> 'a -> bool*)

(*val unsafe_structural_inequality : forall 'a. 'a -> 'a -> bool*)
(*let unsafe_structural_inequality x y=  not (unsafe_structural_equality x y)*)


(* ========================================================================== *)
(* Orderings                                                                  *)
(* ========================================================================== *)

(* The type-class Ord represents total orders (also called linear orders) *)
datatype ordering = LT | EQ | GT

fun orderingIsLess  :: " ordering \<Rightarrow> bool "        where 
     " orderingIsLess LT       = ( True )"
|" orderingIsLess _       = ( False )"

fun orderingIsGreater  :: " ordering \<Rightarrow> bool "     where 
     " orderingIsGreater GT    = ( True )"
|" orderingIsGreater _    = ( False )"

fun orderingIsEqual  :: " ordering \<Rightarrow> bool "       where 
     " orderingIsEqual EQ      = ( True )"
|" orderingIsEqual _      = ( False )"


definition ordering_cases  :: " ordering \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a "  where 
     " ordering_cases r lt eq gt = (
  if orderingIsLess r then lt else
  if orderingIsEqual r then eq else gt )"



(*val orderingEqual : ordering -> ordering -> bool*)

datatype_record 'a Ord_class= 
 
  compare_method                 ::" 'a \<Rightarrow> 'a \<Rightarrow> ordering " 

  isLess_method         ::" 'a \<Rightarrow> 'a \<Rightarrow> bool " 

  isLessEqual_method    ::" 'a \<Rightarrow> 'a \<Rightarrow> bool " 

  isGreater_method      ::" 'a \<Rightarrow> 'a \<Rightarrow> bool " 

  isGreaterEqual_method ::" 'a \<Rightarrow> 'a \<Rightarrow> bool " 




(* Ocaml provides default, polymorphic compare functions. Let's use them
   as the default. However, because used perhaps in a typeclass they must be 
   defined for all targets. So, explicitly declare them as undefined for
   all other targets. If explictly declare undefined, the type-checker won't complain and
   an error will only be raised when trying to actually output the function for a certain
   target. *)
(*val defaultCompare   : forall 'a. 'a -> 'a -> ordering*)
(*val defaultLess      : forall 'a. 'a -> 'a -> bool*)
(*val defaultLessEq    : forall 'a. 'a -> 'a -> bool*)
(*val defaultGreater   : forall 'a. 'a -> 'a -> bool*)
(*val defaultGreaterEq : forall 'a. 'a -> 'a -> bool*) 


definition genericCompare  :: "('a \<Rightarrow> 'a \<Rightarrow> bool)\<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool)\<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ordering "  where 
     " genericCompare (less1:: 'a \<Rightarrow> 'a \<Rightarrow> bool) (equal:: 'a \<Rightarrow> 'a \<Rightarrow> bool) (x :: 'a) (y :: 'a) = (
  if less1 x y then
    LT
  else if equal x y then
    EQ
  else
    GT )"



(*
(* compare should really be a total order *)
lemma ord_OK_1: (
  (forall x y. (compare x y = EQ) <-> (compare y x = EQ)) &&
  (forall x y. (compare x y = LT) <-> (compare y x = GT)))

lemma ord_OK_2: (
  (forall x y z. (x <= y) && (y <= z) --> (x <= z)) &&
  (forall x y. (x <= y) || (y <= x))
)
*)

(* let's derive a compare function from the Ord type-class *)
(*val ordCompare : forall 'a. Eq 'a, Ord 'a => 'a -> 'a -> ordering*)
definition ordCompare  :: " 'a Ord_class \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ordering "  where 
     " ordCompare dict_Basic_classes_Ord_a x y = (
  if ((isLess_method   dict_Basic_classes_Ord_a) x y) then LT else
  if (x = y) then EQ else GT )"


datatype_record 'a OrdMaxMin_class= 
 
  max_method ::" 'a \<Rightarrow> 'a \<Rightarrow> 'a " 

  min_method ::" 'a \<Rightarrow> 'a \<Rightarrow> 'a "



(*val minByLessEqual : forall 'a. ('a -> 'a -> bool) -> 'a -> 'a -> 'a*)

(*val maxByLessEqual : forall 'a. ('a -> 'a -> bool) -> 'a -> 'a -> 'a*)

(*val defaultMax : forall 'a. Ord 'a => 'a -> 'a -> 'a*)

(*val defaultMin : forall 'a. Ord 'a => 'a -> 'a -> 'a*)

definition instance_Basic_classes_OrdMaxMin_var_dict  :: " 'a Ord_class \<Rightarrow> 'a OrdMaxMin_class "  where 
     " instance_Basic_classes_OrdMaxMin_var_dict dict_Basic_classes_Ord_a = ((|

  max_method = ((\<lambda> x y. if (
  (isLessEqual_method   dict_Basic_classes_Ord_a) y x) then x else y)),

  min_method = ((\<lambda> x y. if (
  (isLessEqual_method   dict_Basic_classes_Ord_a) x y) then x else y))|) )"



(* ========================================================================== *)
(* SetTypes                                                                   *)
(* ========================================================================== *)

(* Set implementations use often an order on the elements. This allows the OCaml implementation
   to use trees for implementing them. At least, one needs to be able to check equality on sets.
   One could use the Ord type-class for sets. However, defining a special typeclass is cleaner
   and allows more flexibility. One can make e.g. sure, that this type-class is ignored for
   backends like HOL or Isabelle, which don't need it. Moreover, one is not forced to also instantiate
   the functions <, <= ... *)

(*class ( SetType 'a ) 
  val {ocaml;coq} setElemCompare : 'a -> 'a -> ordering
end*)

fun boolCompare  :: " bool \<Rightarrow> bool \<Rightarrow> ordering "  where 
     " boolCompare True True = ( EQ )"
|" boolCompare True False = ( GT )"
|" boolCompare False True = ( LT )"
|" boolCompare False False = ( EQ )"


(* strings *)

(*val charEqual : char -> char -> bool*)

(*val stringEquality : string -> string -> bool*)

(* pairs *)

(*val pairEqual : forall 'a 'b. Eq 'a, Eq 'b => ('a * 'b) -> ('a * 'b) -> bool*)
(*let pairEqual (a1, b1) (a2, b2)=  (a1 = a2) && (b1 = b2)*)

(*val pairEqualBy : forall 'a 'b. ('a -> 'a -> bool) -> ('b -> 'b -> bool) -> ('a * 'b) -> ('a * 'b) -> bool*)

(*val pairCompare : forall 'a 'b. ('a -> 'a -> ordering) -> ('b -> 'b -> ordering) -> ('a * 'b) -> ('a * 'b) -> ordering*)
fun pairCompare  :: "('a \<Rightarrow> 'a \<Rightarrow> ordering)\<Rightarrow>('b \<Rightarrow> 'b \<Rightarrow> ordering)\<Rightarrow> 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> ordering "  where 
     " pairCompare cmpa cmpb (a1, b1) (a2, b2) = (
  (case  cmpa a1 a2 of
      LT => LT
    | GT => GT
    | EQ => cmpb b1 b2
  ))"


fun pairLess  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'b*'a \<Rightarrow> 'b*'a \<Rightarrow> bool "  where 
     " pairLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b (x1, x2) (y1, y2) = ( (
  (isLess_method   dict_Basic_classes_Ord_b) x1 y1) \<or> (((isLessEqual_method   dict_Basic_classes_Ord_b) x1 y1) \<and> ((isLess_method   dict_Basic_classes_Ord_a) x2 y2)))"

fun pairLessEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'b*'a \<Rightarrow> 'b*'a \<Rightarrow> bool "  where 
     " pairLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b (x1, x2) (y1, y2) = ( (
  (isLess_method   dict_Basic_classes_Ord_b) x1 y1) \<or> (((isLessEqual_method   dict_Basic_classes_Ord_b) x1 y1) \<and> ((isLessEqual_method   dict_Basic_classes_Ord_a) x2 y2)))"


definition pairGreater  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool "  where 
     " pairGreater dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b x12 y12 = ( pairLess 
  dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y12 x12 )"

definition pairGreaterEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool "  where 
     " pairGreaterEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b x12 y12 = ( pairLessEq 
  dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y12 x12 )"


definition instance_Basic_classes_Ord_tup2_dict  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow>('a*'b)Ord_class "  where 
     " instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b = ((|

  compare_method = (pairCompare 
  (compare_method   dict_Basic_classes_Ord_a) (compare_method   dict_Basic_classes_Ord_b)),

  isLess_method = 
  (pairLess dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a),

  isLessEqual_method = 
  (pairLessEq dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a),

  isGreater_method = 
  (pairGreater dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b),

  isGreaterEqual_method = 
  (pairGreaterEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b) |) )"



(* triples *)

(*val tripleEqual : forall 'a 'b 'c. Eq 'a, Eq 'b, Eq 'c => ('a * 'b * 'c) -> ('a * 'b * 'c) -> bool*)
(*let tripleEqual (x1, x2, x3) (y1, y2, y3)=  ((Instance_Basic_classes_Eq_tup2.=) (x1, (x2, x3)) (y1, (y2, y3)))*)

(*val tripleCompare : forall 'a 'b 'c. ('a -> 'a -> ordering) -> ('b -> 'b -> ordering) -> ('c -> 'c -> ordering) -> ('a * 'b * 'c) -> ('a * 'b * 'c) -> ordering*)
fun tripleCompare  :: "('a \<Rightarrow> 'a \<Rightarrow> ordering)\<Rightarrow>('b \<Rightarrow> 'b \<Rightarrow> ordering)\<Rightarrow>('c \<Rightarrow> 'c \<Rightarrow> ordering)\<Rightarrow> 'a*'b*'c \<Rightarrow> 'a*'b*'c \<Rightarrow> ordering "  where 
     " tripleCompare cmpa cmpb cmpc (a1, b1, c1) (a2, b2, c2) = (
  pairCompare cmpa (pairCompare cmpb cmpc) (a1, (b1, c1)) (a2, (b2, c2)))"


fun tripleLess  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'a*'b*'c \<Rightarrow> 'a*'b*'c \<Rightarrow> bool "  where 
     " tripleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c (x1, x2, x3) (y1, y2, y3) = ( pairLess 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c) dict_Basic_classes_Ord_a (x1, (x2, x3)) (y1, (y2, y3)))"

fun tripleLessEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'a*'b*'c \<Rightarrow> 'a*'b*'c \<Rightarrow> bool "  where 
     " tripleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c (x1, x2, x3) (y1, y2, y3) = ( pairLessEq 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c) dict_Basic_classes_Ord_a (x1, (x2, x3)) (y1, (y2, y3)))"


definition tripleGreater  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'c*'b*'a \<Rightarrow> 'c*'b*'a \<Rightarrow> bool "  where 
     " tripleGreater dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c x123 y123 = ( tripleLess 
  dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y123 x123 )"

definition tripleGreaterEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'c*'b*'a \<Rightarrow> 'c*'b*'a \<Rightarrow> bool "  where 
     " tripleGreaterEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c x123 y123 = ( tripleLessEq 
  dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y123 x123 )"


definition instance_Basic_classes_Ord_tup3_dict  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow>('a*'b*'c)Ord_class "  where 
     " instance_Basic_classes_Ord_tup3_dict dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c = ((|

  compare_method = (tripleCompare 
  (compare_method   dict_Basic_classes_Ord_a) (compare_method   dict_Basic_classes_Ord_b) (compare_method   dict_Basic_classes_Ord_c)),

  isLess_method = 
  (tripleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c),

  isLessEqual_method = 
  (tripleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c),

  isGreater_method = 
  (tripleGreater dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_a),

  isGreaterEqual_method = 
  (tripleGreaterEq dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_a) |) )"


(* quadruples *)

(*val quadrupleEqual : forall 'a 'b 'c 'd. Eq 'a, Eq 'b, Eq 'c, Eq 'd => ('a * 'b * 'c * 'd) -> ('a * 'b * 'c * 'd) -> bool*)
(*let quadrupleEqual (x1, x2, x3, x4) (y1, y2, y3, y4)=  ((Instance_Basic_classes_Eq_tup2.=) (x1, (x2, (x3, x4))) (y1, (y2, (y3, y4))))*)

(*val quadrupleCompare : forall 'a 'b 'c 'd. ('a -> 'a -> ordering) -> ('b -> 'b -> ordering) -> ('c -> 'c -> ordering) ->
                                              ('d -> 'd -> ordering) -> ('a * 'b * 'c * 'd) -> ('a * 'b * 'c * 'd) -> ordering*)
fun quadrupleCompare  :: "('a \<Rightarrow> 'a \<Rightarrow> ordering)\<Rightarrow>('b \<Rightarrow> 'b \<Rightarrow> ordering)\<Rightarrow>('c \<Rightarrow> 'c \<Rightarrow> ordering)\<Rightarrow>('d \<Rightarrow> 'd \<Rightarrow> ordering)\<Rightarrow> 'a*'b*'c*'d \<Rightarrow> 'a*'b*'c*'d \<Rightarrow> ordering "  where 
     " quadrupleCompare cmpa cmpb cmpc cmpd (a1, b1, c1, d1) (a2, b2, c2, d2) = (
  pairCompare cmpa (pairCompare cmpb (pairCompare cmpc cmpd)) (a1, (b1, (c1, d1))) (a2, (b2, (c2, d2))))"


fun quadrupleLess  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'a*'b*'c*'d \<Rightarrow> 'a*'b*'c*'d \<Rightarrow> bool "  where 
     " quadrupleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d (x1, x2, x3, x4) (y1, y2, y3, y4) = ( pairLess 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_c
        dict_Basic_classes_Ord_d)) dict_Basic_classes_Ord_a (x1, (x2, (x3, x4))) (y1, (y2, (y3, y4))))"

fun quadrupleLessEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'a*'b*'c*'d \<Rightarrow> 'a*'b*'c*'d \<Rightarrow> bool "  where 
     " quadrupleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d (x1, x2, x3, x4) (y1, y2, y3, y4) = ( pairLessEq 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_c
        dict_Basic_classes_Ord_d)) dict_Basic_classes_Ord_a (x1, (x2, (x3, x4))) (y1, (y2, (y3, y4))))"


definition quadrupleGreater  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'd*'c*'b*'a \<Rightarrow> 'd*'c*'b*'a \<Rightarrow> bool "  where 
     " quadrupleGreater dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d x1234 y1234 = ( quadrupleLess 
  dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y1234 x1234 )"

definition quadrupleGreaterEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'd*'c*'b*'a \<Rightarrow> 'd*'c*'b*'a \<Rightarrow> bool "  where 
     " quadrupleGreaterEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d x1234 y1234 = ( quadrupleLessEq 
  dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y1234 x1234 )"


definition instance_Basic_classes_Ord_tup4_dict  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow>('a*'b*'c*'d)Ord_class "  where 
     " instance_Basic_classes_Ord_tup4_dict dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d = ((|

  compare_method = (quadrupleCompare 
  (compare_method   dict_Basic_classes_Ord_a) (compare_method   dict_Basic_classes_Ord_b) (compare_method   dict_Basic_classes_Ord_c) (compare_method   dict_Basic_classes_Ord_d)),

  isLess_method = 
  (quadrupleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d),

  isLessEqual_method = 
  (quadrupleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d),

  isGreater_method = 
  (quadrupleGreater dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c
     dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a),

  isGreaterEqual_method = 
  (quadrupleGreaterEq dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c
     dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a) |) )"


(* quintuples *)

(*val quintupleEqual : forall 'a 'b 'c 'd 'e. Eq 'a, Eq 'b, Eq 'c, Eq 'd, Eq 'e => ('a * 'b * 'c * 'd * 'e) -> ('a * 'b * 'c * 'd * 'e) -> bool*)
(*let quintupleEqual (x1, x2, x3, x4, x5) (y1, y2, y3, y4, y5)=  ((Instance_Basic_classes_Eq_tup2.=) (x1, (x2, (x3, (x4, x5)))) (y1, (y2, (y3, (y4, y5)))))*)

(*val quintupleCompare : forall 'a 'b 'c 'd 'e. ('a -> 'a -> ordering) -> ('b -> 'b -> ordering) -> ('c -> 'c -> ordering) ->
                                              ('d -> 'd -> ordering) -> ('e -> 'e -> ordering) -> ('a * 'b * 'c * 'd * 'e) -> ('a * 'b * 'c * 'd * 'e) -> ordering*)
fun quintupleCompare  :: "('a \<Rightarrow> 'a \<Rightarrow> ordering)\<Rightarrow>('b \<Rightarrow> 'b \<Rightarrow> ordering)\<Rightarrow>('c \<Rightarrow> 'c \<Rightarrow> ordering)\<Rightarrow>('d \<Rightarrow> 'd \<Rightarrow> ordering)\<Rightarrow>('e \<Rightarrow> 'e \<Rightarrow> ordering)\<Rightarrow> 'a*'b*'c*'d*'e \<Rightarrow> 'a*'b*'c*'d*'e \<Rightarrow> ordering "  where 
     " quintupleCompare cmpa cmpb cmpc cmpd cmpe (a1, b1, c1, d1, e1) (a2, b2, c2, d2, e2) = (
  pairCompare cmpa (pairCompare cmpb (pairCompare cmpc (pairCompare cmpd cmpe))) (a1, (b1, (c1, (d1, e1)))) (a2, (b2, (c2, (d2, e2)))))"


fun quintupleLess  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'a*'b*'c*'d*'e \<Rightarrow> 'a*'b*'c*'d*'e \<Rightarrow> bool "  where 
     " quintupleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e (x1, x2, x3, x4, x5) (y1, y2, y3, y4, y5) = ( pairLess 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_c
        (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_d
           dict_Basic_classes_Ord_e))) dict_Basic_classes_Ord_a (x1, (x2, (x3, (x4, x5)))) (y1, (y2, (y3, (y4, y5)))))"

fun quintupleLessEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'a*'b*'c*'d*'e \<Rightarrow> 'a*'b*'c*'d*'e \<Rightarrow> bool "  where 
     " quintupleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e (x1, x2, x3, x4, x5) (y1, y2, y3, y4, y5) = ( pairLessEq 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_c
        (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_d
           dict_Basic_classes_Ord_e))) dict_Basic_classes_Ord_a (x1, (x2, (x3, (x4, x5)))) (y1, (y2, (y3, (y4, y5)))))"


definition quintupleGreater  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'e*'d*'c*'b*'a \<Rightarrow> 'e*'d*'c*'b*'a \<Rightarrow> bool "  where 
     " quintupleGreater dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e x12345 y12345 = ( quintupleLess 
  dict_Basic_classes_Ord_e dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y12345 x12345 )"

definition quintupleGreaterEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'e*'d*'c*'b*'a \<Rightarrow> 'e*'d*'c*'b*'a \<Rightarrow> bool "  where 
     " quintupleGreaterEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e x12345 y12345 = ( quintupleLessEq 
  dict_Basic_classes_Ord_e dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y12345 x12345 )"


definition instance_Basic_classes_Ord_tup5_dict  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow>('a*'b*'c*'d*'e)Ord_class "  where 
     " instance_Basic_classes_Ord_tup5_dict dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e = ((|

  compare_method = (quintupleCompare 
  (compare_method   dict_Basic_classes_Ord_a) (compare_method   dict_Basic_classes_Ord_b) (compare_method   dict_Basic_classes_Ord_c) (compare_method   dict_Basic_classes_Ord_d) (compare_method   dict_Basic_classes_Ord_e)),

  isLess_method = 
  (quintupleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d
     dict_Basic_classes_Ord_e),

  isLessEqual_method = 
  (quintupleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d
     dict_Basic_classes_Ord_e),

  isGreater_method = 
  (quintupleGreater dict_Basic_classes_Ord_e dict_Basic_classes_Ord_d
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_a),

  isGreaterEqual_method = 
  (quintupleGreaterEq dict_Basic_classes_Ord_e dict_Basic_classes_Ord_d
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_a) |) )"


(* sextuples *)

(*val sextupleEqual : forall 'a 'b 'c 'd 'e 'f. Eq 'a, Eq 'b, Eq 'c, Eq 'd, Eq 'e, Eq 'f => ('a * 'b * 'c * 'd * 'e * 'f) -> ('a * 'b * 'c * 'd * 'e * 'f) -> bool*)
(*let sextupleEqual (x1, x2, x3, x4, x5, x6) (y1, y2, y3, y4, y5, y6)=  ((Instance_Basic_classes_Eq_tup2.=) (x1, (x2, (x3, (x4, (x5, x6))))) (y1, (y2, (y3, (y4, (y5, y6))))))*)

(*val sextupleCompare : forall 'a 'b 'c 'd 'e 'f. ('a -> 'a -> ordering) -> ('b -> 'b -> ordering) -> ('c -> 'c -> ordering) ->
                                              ('d -> 'd -> ordering) -> ('e -> 'e -> ordering) -> ('f -> 'f -> ordering) ->
                                              ('a * 'b * 'c * 'd * 'e * 'f) -> ('a * 'b * 'c * 'd * 'e * 'f) -> ordering*)
fun sextupleCompare  :: "('a \<Rightarrow> 'a \<Rightarrow> ordering)\<Rightarrow>('b \<Rightarrow> 'b \<Rightarrow> ordering)\<Rightarrow>('c \<Rightarrow> 'c \<Rightarrow> ordering)\<Rightarrow>('d \<Rightarrow> 'd \<Rightarrow> ordering)\<Rightarrow>('e \<Rightarrow> 'e \<Rightarrow> ordering)\<Rightarrow>('f \<Rightarrow> 'f \<Rightarrow> ordering)\<Rightarrow> 'a*'b*'c*'d*'e*'f \<Rightarrow> 'a*'b*'c*'d*'e*'f \<Rightarrow> ordering "  where 
     " sextupleCompare cmpa cmpb cmpc cmpd cmpe cmpf (a1, b1, c1, d1, e1, f1) (a2, b2, c2, d2, e2, f2) = (
  pairCompare cmpa (pairCompare cmpb (pairCompare cmpc (pairCompare cmpd (pairCompare cmpe cmpf)))) (a1, (b1, (c1, (d1, (e1, f1))))) (a2, (b2, (c2, (d2, (e2, f2))))))"


fun sextupleLess  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'f Ord_class \<Rightarrow> 'a*'b*'c*'d*'e*'f \<Rightarrow> 'a*'b*'c*'d*'e*'f \<Rightarrow> bool "  where 
     " sextupleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f (x1, x2, x3, x4, x5, x6) (y1, y2, y3, y4, y5, y6) = ( pairLess 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_c
        (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_d
           (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_e
              dict_Basic_classes_Ord_f)))) dict_Basic_classes_Ord_a (x1, (x2, (x3, (x4, (x5, x6))))) (y1, (y2, (y3, (y4, (y5, y6))))))"

fun sextupleLessEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'f Ord_class \<Rightarrow> 'a*'b*'c*'d*'e*'f \<Rightarrow> 'a*'b*'c*'d*'e*'f \<Rightarrow> bool "  where 
     " sextupleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f (x1, x2, x3, x4, x5, x6) (y1, y2, y3, y4, y5, y6) = ( pairLessEq 
  (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_b
     (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_c
        (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_d
           (instance_Basic_classes_Ord_tup2_dict dict_Basic_classes_Ord_e
              dict_Basic_classes_Ord_f)))) dict_Basic_classes_Ord_a (x1, (x2, (x3, (x4, (x5, x6))))) (y1, (y2, (y3, (y4, (y5, y6))))))"


definition sextupleGreater  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'f Ord_class \<Rightarrow> 'f*'e*'d*'c*'b*'a \<Rightarrow> 'f*'e*'d*'c*'b*'a \<Rightarrow> bool "  where 
     " sextupleGreater dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f x123456 y123456 = ( sextupleLess 
  dict_Basic_classes_Ord_f dict_Basic_classes_Ord_e dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y123456 x123456 )"

definition sextupleGreaterEq  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'f Ord_class \<Rightarrow> 'f*'e*'d*'c*'b*'a \<Rightarrow> 'f*'e*'d*'c*'b*'a \<Rightarrow> bool "  where 
     " sextupleGreaterEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f x123456 y123456 = ( sextupleLessEq 
  dict_Basic_classes_Ord_f dict_Basic_classes_Ord_e dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a y123456 x123456 )"


definition instance_Basic_classes_Ord_tup6_dict  :: " 'a Ord_class \<Rightarrow> 'b Ord_class \<Rightarrow> 'c Ord_class \<Rightarrow> 'd Ord_class \<Rightarrow> 'e Ord_class \<Rightarrow> 'f Ord_class \<Rightarrow>('a*'b*'c*'d*'e*'f)Ord_class "  where 
     " instance_Basic_classes_Ord_tup6_dict dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f = ((|

  compare_method = (sextupleCompare 
  (compare_method   dict_Basic_classes_Ord_a) (compare_method   dict_Basic_classes_Ord_b) (compare_method   dict_Basic_classes_Ord_c) (compare_method   dict_Basic_classes_Ord_d) (compare_method   dict_Basic_classes_Ord_e) (compare_method   dict_Basic_classes_Ord_f)),

  isLess_method = 
  (sextupleLess dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d
     dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f),

  isLessEqual_method = 
  (sextupleLessEq dict_Basic_classes_Ord_a dict_Basic_classes_Ord_b
     dict_Basic_classes_Ord_c dict_Basic_classes_Ord_d
     dict_Basic_classes_Ord_e dict_Basic_classes_Ord_f),

  isGreater_method = 
  (sextupleGreater dict_Basic_classes_Ord_f dict_Basic_classes_Ord_e
     dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c
     dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a),

  isGreaterEqual_method = 
  (sextupleGreaterEq dict_Basic_classes_Ord_f dict_Basic_classes_Ord_e
     dict_Basic_classes_Ord_d dict_Basic_classes_Ord_c
     dict_Basic_classes_Ord_b dict_Basic_classes_Ord_a) |) )"

end
