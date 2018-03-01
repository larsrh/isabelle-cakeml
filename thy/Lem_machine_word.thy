chapter \<open>Generated by Lem from machine_word.lem.\<close>

theory "Lem_machine_word" 

imports 
 	 Main
	 "Lem_bool" 
	 "Lem_num" 
	 "Lem_basic_classes" 
	 "Lem_show" 
	 "HOL-Word.Word" 

begin 



(*open import Bool Num Basic_classes Show*)

(*open import {isabelle} `HOL-Word.Word`*)
(*open import {hol} `wordsTheory` `wordsLib` `bitstringTheory` `integer_wordTheory`*)

(*type mword 'a*)

(*class (Size 'a)
  val size : nat
end*)

(*val native_size : forall 'a. nat*)

(*val ocaml_inject : forall 'a. nat * natural -> mword 'a*)

(* A singleton type family that can be used to carry a size as the type parameter *)

(*type itself 'a*)

(*val the_value : forall 'a. itself 'a*)

(*val size_itself : forall 'a. Size 'a => itself 'a -> nat*)
definition size_itself  :: "('a::len)itself \<Rightarrow> nat "  where 
     " size_itself x = ( (len_of (TYPE(_) :: 'a itself)))"


(*******************************************************************)
(* Fixed bitwidths extracted from Anthony's models.                *)
(*                                                                 *)
(* If you need a size N that is not included here, put the lines   *)
(*                                                                 *)
(* type tyN                                                        *)
(* instance (Size tyN) let size = N end                            *)
(* declare isabelle target_rep type tyN = `N`                      *)
(* declare hol target_rep type tyN = `N`                           *)
(*                                                                 *)
(* in your project, replacing N in each line.                      *)
(*******************************************************************)

(*type ty1*)
(*type ty2*)
(*type ty3*)
(*type ty4*)
(*type ty5*)
(*type ty6*)
(*type ty7*)
(*type ty8*)
(*type ty9*)
(*type ty10*)
(*type ty11*)
(*type ty12*)
(*type ty13*)
(*type ty14*)
(*type ty15*)
(*type ty16*)
(*type ty17*)
(*type ty18*)
(*type ty19*)
(*type ty20*)
(*type ty21*)
(*type ty22*)
(*type ty23*)
(*type ty24*)
(*type ty25*)
(*type ty26*)
(*type ty27*)
(*type ty28*)
(*type ty29*)
(*type ty30*)
(*type ty31*)
(*type ty32*)
(*type ty33*)
(*type ty34*)
(*type ty35*)
(*type ty36*)
(*type ty37*)
(*type ty38*)
(*type ty39*)
(*type ty40*)
(*type ty41*)
(*type ty42*)
(*type ty43*)
(*type ty44*)
(*type ty45*)
(*type ty46*)
(*type ty47*)
(*type ty48*)
(*type ty49*)
(*type ty50*)
(*type ty51*)
(*type ty52*)
(*type ty53*)
(*type ty54*)
(*type ty55*)
(*type ty56*)
(*type ty57*)
(*type ty58*)
(*type ty59*)
(*type ty60*)
(*type ty61*)
(*type ty62*)
(*type ty63*)
(*type ty64*)
(*type ty65*)
(*type ty66*)
(*type ty67*)
(*type ty68*)
(*type ty69*)
(*type ty70*)
(*type ty71*)
(*type ty72*)
(*type ty73*)
(*type ty74*)
(*type ty75*)
(*type ty76*)
(*type ty77*)
(*type ty78*)
(*type ty79*)
(*type ty80*)
(*type ty81*)
(*type ty82*)
(*type ty83*)
(*type ty84*)
(*type ty85*)
(*type ty86*)
(*type ty87*)
(*type ty88*)
(*type ty89*)
(*type ty90*)
(*type ty91*)
(*type ty92*)
(*type ty93*)
(*type ty94*)
(*type ty95*)
(*type ty96*)
(*type ty97*)
(*type ty98*)
(*type ty99*)
(*type ty100*)
(*type ty101*)
(*type ty102*)
(*type ty103*)
(*type ty104*)
(*type ty105*)
(*type ty106*)
(*type ty107*)
(*type ty108*)
(*type ty109*)
(*type ty110*)
(*type ty111*)
(*type ty112*)
(*type ty113*)
(*type ty114*)
(*type ty115*)
(*type ty116*)
(*type ty117*)
(*type ty118*)
(*type ty119*)
(*type ty120*)
(*type ty121*)
(*type ty122*)
(*type ty123*)
(*type ty124*)
(*type ty125*)
(*type ty126*)
(*type ty127*)
(*type ty128*)
(*type ty129*)
(*type ty130*)
(*type ty131*)
(*type ty132*)
(*type ty133*)
(*type ty134*)
(*type ty135*)
(*type ty136*)
(*type ty137*)
(*type ty138*)
(*type ty139*)
(*type ty140*)
(*type ty141*)
(*type ty142*)
(*type ty143*)
(*type ty144*)
(*type ty145*)
(*type ty146*)
(*type ty147*)
(*type ty148*)
(*type ty149*)
(*type ty150*)
(*type ty151*)
(*type ty152*)
(*type ty153*)
(*type ty154*)
(*type ty155*)
(*type ty156*)
(*type ty157*)
(*type ty158*)
(*type ty159*)
(*type ty160*)
(*type ty161*)
(*type ty162*)
(*type ty163*)
(*type ty164*)
(*type ty165*)
(*type ty166*)
(*type ty167*)
(*type ty168*)
(*type ty169*)
(*type ty170*)
(*type ty171*)
(*type ty172*)
(*type ty173*)
(*type ty174*)
(*type ty175*)
(*type ty176*)
(*type ty177*)
(*type ty178*)
(*type ty179*)
(*type ty180*)
(*type ty181*)
(*type ty182*)
(*type ty183*)
(*type ty184*)
(*type ty185*)
(*type ty186*)
(*type ty187*)
(*type ty188*)
(*type ty189*)
(*type ty190*)
(*type ty191*)
(*type ty192*)
(*type ty193*)
(*type ty194*)
(*type ty195*)
(*type ty196*)
(*type ty197*)
(*type ty198*)
(*type ty199*)
(*type ty200*)
(*type ty201*)
(*type ty202*)
(*type ty203*)
(*type ty204*)
(*type ty205*)
(*type ty206*)
(*type ty207*)
(*type ty208*)
(*type ty209*)
(*type ty210*)
(*type ty211*)
(*type ty212*)
(*type ty213*)
(*type ty214*)
(*type ty215*)
(*type ty216*)
(*type ty217*)
(*type ty218*)
(*type ty219*)
(*type ty220*)
(*type ty221*)
(*type ty222*)
(*type ty223*)
(*type ty224*)
(*type ty225*)
(*type ty226*)
(*type ty227*)
(*type ty228*)
(*type ty229*)
(*type ty230*)
(*type ty231*)
(*type ty232*)
(*type ty233*)
(*type ty234*)
(*type ty235*)
(*type ty236*)
(*type ty237*)
(*type ty238*)
(*type ty239*)
(*type ty240*)
(*type ty241*)
(*type ty242*)
(*type ty243*)
(*type ty244*)
(*type ty245*)
(*type ty246*)
(*type ty247*)
(*type ty248*)
(*type ty249*)
(*type ty250*)
(*type ty251*)
(*type ty252*)
(*type ty253*)
(*type ty254*)
(*type ty255*)
(*type ty256*)
(*type ty257*)

(*val word_length : forall 'a. mword 'a -> nat*)

(******************************************************************)
(* Conversions                                                    *)
(******************************************************************)

(*val signedIntegerFromWord : forall 'a. mword 'a -> integer*)

(*val unsignedIntegerFromWord : forall 'a. mword 'a -> integer*)

(* Version without typeclass constraint so that we can derive operations
   in Lem for one of the theorem provers without requiring it. *)
(*val proverWordFromInteger : forall 'a. integer -> mword 'a*)

(*val wordFromInteger : forall 'a. Size 'a => integer -> mword 'a*)
(* The OCaml version is defined after the arithmetic operations, below. *)

(*val naturalFromWord : forall 'a. mword 'a -> natural*)

(*val wordFromNatural : forall 'a. Size 'a => natural -> mword 'a*)

(*val wordToHex : forall 'a. mword 'a -> string*)
(* Building libraries fails if we don't provide implementations for the
   type class. *)
definition wordToHex  :: "('a::len)Word.word \<Rightarrow> string "  where 
     " wordToHex w = ( (''wordToHex not yet implemented''))"


definition instance_Show_Show_Machine_word_mword_dict  :: "(('a::len)Word.word)Show_class "  where 
     " instance_Show_Show_Machine_word_mword_dict = ((|

  show_method = wordToHex |) )"


(*val wordFromBitlist : forall 'a. Size 'a => list bool -> mword 'a*)

(*val bitlistFromWord : forall 'a. mword 'a -> list bool*)


(*val size_test_fn : forall 'a. Size 'a => mword 'a -> nat*)
definition size_test_fn  :: "('a::len)Word.word \<Rightarrow> nat "  where 
     " size_test_fn _ = ( (len_of (TYPE(_) :: 'a itself)))"


(******************************************************************)
(* Comparisons                                                    *)
(******************************************************************)

(*val mwordEq : forall 'a. mword 'a -> mword 'a -> bool*)

(*val signedLess : forall 'a. mword 'a -> mword 'a -> bool*)

(*val signedLessEq : forall 'a. mword 'a -> mword 'a -> bool*)

(*val unsignedLess : forall 'a. mword 'a -> mword 'a -> bool*)

(*val unsignedLessEq : forall 'a. mword 'a -> mword 'a -> bool*)

(* Comparison tests are below, after the definition of wordFromInteger *)

(******************************************************************)
(* Appending, splitting and probing words                         *)
(******************************************************************)

(*val word_concat : forall 'a 'b 'c. mword 'a -> mword 'b -> mword 'c*)

(* Note that we assume the result type has the correct size, especially
   for Isabelle. *)
(*val word_extract : forall 'a 'b. nat -> nat -> mword 'a -> mword 'b*)

(*  Needs to be in the prover because we'd end up with unknown sizes in the
   types in Lem.
*)
(*val word_update : forall 'a 'b. mword 'a -> nat -> nat -> mword 'b -> mword 'a*)

(*val setBit : forall 'a. mword 'a -> nat -> bool -> mword 'a*)

(*val getBit : forall 'a. mword 'a -> nat -> bool*)

(*val msb : forall 'a. mword 'a -> bool*)

(*val lsb : forall 'a. mword 'a -> bool*)

(******************************************************************)
(* Bitwise operations, shifts, etc.                               *)
(******************************************************************)

(*val shiftLeft  : forall 'a. mword 'a -> nat -> mword 'a*)

(*val shiftRight : forall 'a. mword 'a -> nat -> mword 'a*)

(*val arithShiftRight : forall 'a. mword 'a -> nat -> mword 'a*)

(*val lAnd       : forall 'a. mword 'a -> mword 'a -> mword 'a*)

(*val lOr        : forall 'a. mword 'a -> mword 'a -> mword 'a*)

(*val lXor       : forall 'a. mword 'a -> mword 'a -> mword 'a*)

(*val lNot       : forall 'a. mword 'a -> mword 'a*)

(*val rotateRight : forall 'a. nat -> mword 'a -> mword 'a*)

(*val rotateLeft : forall 'a. nat -> mword 'a -> mword 'a*)

(*val zeroExtend : forall 'a 'b. Size 'b => mword 'a -> mword 'b*)

(*val signExtend : forall 'a 'b. Size 'b => mword 'a -> mword 'b*)

(* Sign extension tests are below, after the definition of wordFromInteger *)

(*****************************************************************)
(* Arithmetic                                                    *)
(*****************************************************************)

(*val plus   : forall 'a. mword 'a -> mword 'a -> mword 'a*)

(*val minus  : forall 'a. mword 'a -> mword 'a -> mword 'a*)

(*val uminus : forall 'a. mword 'a -> mword 'a*)

(*val times : forall 'a. mword 'a -> mword 'a -> mword 'a*)

(*val unsignedDivide : forall 'a. mword 'a -> mword 'a -> mword 'a*)
(*val signedDivide : forall 'a. mword 'a -> mword 'a -> mword 'a*)

definition signedDivide  :: "('a::len)Word.word \<Rightarrow>('a::len)Word.word \<Rightarrow>('a::len)Word.word "  where 
     " signedDivide x y = (
  Word.word_of_int ((Word.sint x) div (Word.sint y)))"


(*val modulo : forall 'a. mword 'a -> mword 'a -> mword 'a*)
end
