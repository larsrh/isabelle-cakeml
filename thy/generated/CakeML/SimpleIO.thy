chapter \<open>Generated by Lem from semantics/ffi/simpleIO.lem.\<close>

theory "SimpleIO" 

imports 
 	 Main
	 "LEM.Lem_pervasives" 
	 "Lib" 
	 "LEM.Lem_pervasives_extra" 
	 "Ffi" 

begin 

(*open import Pervasives*)
(*open import Pervasives_extra*)
(*open import Lib*)
(*open import Ffi*)

datatype_record simpleIO = 
 input ::"  8 word llist " 
 output0 ::"  8 word llist " 


(*val isEof : oracle_function simpleIO*)
fun isEof  :: " simpleIO \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow>(simpleIO)oracle_result "  where 
     " isEof st conf ([]) = ( Oracle_fail )"
|" isEof st conf (x # xs) = ( Oracle_return st ((if(input   st) = LNil then of_nat (( 1 :: nat)) else of_nat (( 0 :: nat)))# xs))"


(*val getChar : oracle_function simpleIO*)
fun getChar  :: " simpleIO \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow>(simpleIO)oracle_result "  where 
     " getChar st conf ([]) = ( Oracle_fail )"
|" getChar st conf (x # xs) = (
      (case  lhd'(input   st) of
        Some y => Oracle_return (( st (| input := (Option.the (ltl'(input   st))) |))) (y # xs)
      | _ => Oracle_fail
      ))"


(*val putChar : oracle_function simpleIO*)
definition putChar  :: " simpleIO \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow>(simpleIO)oracle_result "  where 
     " putChar st conf input1 = (
  (case  input1 of
    [] => Oracle_fail
  | x # _ => Oracle_return (( st (| output0 := (LCons x(output0   st)) |))) input1
  ))"


(*val exit : oracle_function simpleIO*)
definition exit0  :: " simpleIO \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow>(simpleIO)oracle_result "  where 
     " exit0 st conf input1 = ( Oracle_diverge )"


(*val simpleIO_oracle : oracle simpleIO*)
definition simpleIO_oracle  :: " string \<Rightarrow> simpleIO \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow>(simpleIO)oracle_result "  where 
     " simpleIO_oracle s st conf input1 = (
  if s = (''isEof'') then
    isEof st conf input1
  else if s = (''getChar'') then
    getChar st conf input1
  else if s = (''putChar'') then
    putChar st conf input1
  else if s = (''exit'') then
    exit0 st conf input1
  else
    Oracle_fail )"

end
