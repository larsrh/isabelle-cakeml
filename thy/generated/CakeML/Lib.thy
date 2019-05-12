chapter \<open>Generated by Lem from \<open>misc/lem_lib_stub/lib.lem\<close>.\<close>

theory "Lib" 

imports
  Main
  "HOL-Library.Datatype_Records"
  "LEM.Lem_pervasives"
  "Coinductive.Coinductive_List"

begin 

\<comment> \<open>\<open>
   Extensions to Lem's built-in library to target things we need in HOL.
\<close>\<close>

\<comment> \<open>\<open>open import Pervasives\<close>\<close>

\<comment> \<open>\<open> TODO: look for these in the built-in library \<close>\<close>

\<comment> \<open>\<open>val rtc : forall 'a. ('a -> 'a -> bool) -> ('a -> 'a -> bool)\<close>\<close>

\<comment> \<open>\<open>val disjoint : forall 'a. set 'a -> set 'a -> bool\<close>\<close>

\<comment> \<open>\<open>val all2 : forall 'a 'b. ('a -> 'b -> bool) -> list 'a -> list 'b -> bool\<close>\<close>
\<comment> \<open>\<open>val map2 : forall 'a 'b 'c. ('a -> 'b -> 'c) -> list 'a -> list 'b -> list 'c\<close>\<close>

fun  the  :: " 'a \<Rightarrow> 'a option \<Rightarrow> 'a "  where 
     " the _ (Some x) = ( x )" |" the x None = ( x )"


\<comment> \<open>\<open>val fapply : forall 'a 'b. MapKeyType 'b => 'a -> 'b -> Map.map 'b 'a -> 'a\<close>\<close>
definition fapply  :: " 'a \<Rightarrow> 'b \<Rightarrow>('b,'a)Map.map \<Rightarrow> 'a "  where 
     " fapply d x f = ( (case   f x of Some d => d | None => d ))"


function (sequential,domintros) 
lunion  :: " 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list "  where 
     "
lunion [] s = ( s )"
|"
lunion (x # xs) s = (
  if Set.member x (set s)
  then lunion xs s
  else x #(lunion xs s))" 
by pat_completeness auto


\<comment> \<open>\<open> TODO: proper support for nat sets as sptrees... \<close>\<close>
\<comment> \<open>\<open>open import {hol} `sptreeTheory`\<close>\<close>
\<comment> \<open>\<open>type nat_set\<close>\<close>
\<comment> \<open>\<open>val nat_set_empty : nat_set\<close>\<close>
\<comment> \<open>\<open>val nat_set_is_empty : nat_set -> bool\<close>\<close>
\<comment> \<open>\<open>val nat_set_insert : nat_set -> nat -> nat_set\<close>\<close>
\<comment> \<open>\<open>val nat_set_delete : nat_set -> nat -> nat_set\<close>\<close>
\<comment> \<open>\<open>val nat_set_to_set : nat_set -> set nat\<close>\<close>
\<comment> \<open>\<open>val nat_set_elem : nat_set -> nat -> bool\<close>\<close>
\<comment> \<open>\<open>val nat_set_from_list : list nat -> nat_set\<close>\<close>
\<comment> \<open>\<open>val nat_set_upto : nat -> nat_set\<close>\<close>

\<comment> \<open>\<open>type nat_map 'a\<close>\<close>
\<comment> \<open>\<open>val nat_map_empty : forall 'a. nat_map 'a\<close>\<close>
\<comment> \<open>\<open>val nat_map_domain : forall 'a. nat_map 'a -> set nat\<close>\<close>
\<comment> \<open>\<open>val nat_map_insert : forall 'a. nat_map 'a -> nat -> 'a -> nat_map 'a\<close>\<close>
\<comment> \<open>\<open>val nat_map_lookup : forall 'a. nat_map 'a -> nat -> maybe 'a\<close>\<close>
\<comment> \<open>\<open>val nat_map_to_list : forall 'a. nat_map 'a -> list 'a\<close>\<close>
\<comment> \<open>\<open>val nat_map_map : forall 'a 'b. ('a -> 'b) -> nat_map 'a -> nat_map 'b\<close>\<close>

\<comment> \<open>\<open> TODO: proper support for lazy lists \<close>\<close>

\<comment> \<open>\<open>open import {hol} `llistTheory`\<close>\<close>
\<comment> \<open>\<open>open import {isabelle} `Coinductive.Coinductive_List`\<close>\<close>
\<comment> \<open>\<open>type llist 'a\<close>\<close>
\<comment> \<open>\<open>val lhd : forall 'a. llist 'a -> maybe 'a\<close>\<close>
\<comment> \<open>\<open>val ltl : forall 'a. llist 'a -> maybe (llist 'a)\<close>\<close>
\<comment> \<open>\<open>val lnil : forall 'a. llist 'a\<close>\<close>
\<comment> \<open>\<open>val lcons : forall 'a. 'a -> llist 'a -> llist 'a\<close>\<close>


\<comment> \<open>\<open> TODO: proper support for words... \<close>\<close>
\<comment> \<open>\<open>open import {hol} `wordsTheory` `integer_wordTheory`\<close>\<close>
\<comment> \<open>\<open>type word8\<close>\<close>
\<comment> \<open>\<open>val natFromWord8 : word8 -> nat\<close>\<close>
\<comment> \<open>\<open>val word_to_hex_string : word8 -> string\<close>\<close>
\<comment> \<open>\<open>val word8FromNat : nat -> word8\<close>\<close>
\<comment> \<open>\<open>val word8FromInteger : integer -> word8\<close>\<close>
\<comment> \<open>\<open>val integerFromWord8 : word8 -> integer\<close>\<close>
\<comment> \<open>\<open>type word64\<close>\<close>
\<comment> \<open>\<open>val natFromWord64 : word64 -> nat\<close>\<close>
\<comment> \<open>\<open>val word64FromNat : nat -> word64\<close>\<close>
\<comment> \<open>\<open>val word64FromInteger : integer -> word64\<close>\<close>
\<comment> \<open>\<open>val integerFromWord64 : word64 -> integer\<close>\<close>
\<comment> \<open>\<open>val word8FromWord64 : word64 -> word8\<close>\<close>
\<comment> \<open>\<open>val word64FromWord8 : word8 -> word64\<close>\<close>
\<comment> \<open>\<open>val W8and : word8 -> word8 -> word8\<close>\<close>
\<comment> \<open>\<open>val W8or : word8 -> word8 -> word8\<close>\<close>
\<comment> \<open>\<open>val W8xor : word8 -> word8 -> word8\<close>\<close>
\<comment> \<open>\<open>val W8add : word8 -> word8 -> word8\<close>\<close>
\<comment> \<open>\<open>val W8sub : word8 -> word8 -> word8\<close>\<close>
\<comment> \<open>\<open>val W64and : word64 -> word64 -> word64\<close>\<close>
\<comment> \<open>\<open>val W64or : word64 -> word64 -> word64\<close>\<close>
\<comment> \<open>\<open>val W64xor : word64 -> word64 -> word64\<close>\<close>
\<comment> \<open>\<open>val W64add : word64 -> word64 -> word64\<close>\<close>
\<comment> \<open>\<open>val W64sub : word64 -> word64 -> word64\<close>\<close>

\<comment> \<open>\<open>val W8lsl : word8 -> nat -> word8\<close>\<close>
\<comment> \<open>\<open>val W8lsr : word8 -> nat -> word8\<close>\<close>
\<comment> \<open>\<open>val W8asr : word8 -> nat -> word8\<close>\<close>
\<comment> \<open>\<open>val W8ror : word8 -> nat -> word8\<close>\<close>
\<comment> \<open>\<open>val W64lsl : word64 -> nat -> word64\<close>\<close>
\<comment> \<open>\<open>val W64lsr : word64 -> nat -> word64\<close>\<close>
\<comment> \<open>\<open>val W64asr : word64 -> nat -> word64\<close>\<close>
\<comment> \<open>\<open>val W64ror : word64 -> nat -> word64\<close>\<close>

\<comment> \<open>\<open>open import {hol} `alistTheory`\<close>\<close>
type_synonym( 'a, 'b) alist =" ('a * 'b) list "
\<comment> \<open>\<open>val alistToFmap : forall 'k 'v. alist 'k 'v -> Map.map 'k 'v\<close>\<close>

\<comment> \<open>\<open>val opt_bind : forall 'a 'b. maybe 'a -> 'b -> alist 'a 'b -> alist 'a 'b\<close>\<close>
fun opt_bind  :: " 'a option \<Rightarrow> 'b \<Rightarrow>('a*'b)list \<Rightarrow>('a*'b)list "  where 
     " opt_bind None v2 e = ( e )"
|" opt_bind (Some n') v2 e = ( (n',v2)# e )"


\<comment> \<open>\<open> Lists of indices \<close>\<close>

fun 
lshift  :: " nat \<Rightarrow>(nat)list \<Rightarrow>(nat)list "  where 
     "
lshift (n :: nat) ls = (
  List.map (\<lambda> v2 .  v2 - n) (List.filter (\<lambda> v2 .  n \<le> v2) ls))"


\<comment> \<open>\<open>open import {hol} `locationTheory`\<close>\<close>
datatype_record locn = 
 row ::" nat " 
  col ::" nat " 
 offset ::" nat " 

type_synonym locs =" (locn * locn)"
\<comment> \<open>\<open>val unknown_loc : locs\<close>\<close>
end
