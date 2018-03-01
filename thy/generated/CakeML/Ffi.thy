chapter \<open>Generated by Lem from semantics/ffi/ffi.lem.\<close>

theory "Ffi" 

imports 
 	 Main
	 "LEM.Lem_pervasives" 
	 "Lib" 
	 "LEM.Lem_pervasives_extra" 

begin 

(*open import Pervasives*)
(*open import Pervasives_extra*)
(*open import Lib*)

(* An oracle says how to perform an ffi call based on its internal state,
* represented by the type variable 'ffi. *)

datatype 'ffi oracle_result = Oracle_return " 'ffi " " 8 word list " | Oracle_diverge | Oracle_fail
type_synonym 'ffi oracle_function =" 'ffi \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 'ffi oracle_result "
type_synonym 'ffi oracle0 =" string \<Rightarrow> 'ffi oracle_function "

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI function s with
* immutable input bytes and mutable input map fst bytes2,
* returning map snd bytes2 in the mutable array. *)

datatype io_event = IO_event " string " " 8 word list " " ( (8 word * 8 word)list)"

datatype ffi_outcome = FFI_diverged | FFI_failed
datatype final_event = Final_event " string " " 8 word list " " 8 word list " " ffi_outcome "

datatype_record 'ffi ffi_state =

 oracle0      ::" 'ffi oracle0 "
 
 ffi_state   ::" 'ffi "
 
 final_event ::"  final_event option "
 
 io_events   ::" io_event list "
 


(*val initial_ffi_state : forall 'ffi. oracle 'ffi -> 'ffi -> ffi_state 'ffi*)
definition initial_ffi_state  :: "(string \<Rightarrow> 'ffi oracle_function)\<Rightarrow> 'ffi \<Rightarrow> 'ffi ffi_state "  where 
     " initial_ffi_state oc ffi1 = (
(| oracle0      = oc
 , ffi_state   = ffi1
 , final_event = None
 , io_events   = ([])
 |) )"


(*val call_FFI : forall 'ffi. ffi_state 'ffi -> string -> list word8 -> list word8 -> ffi_state 'ffi * list word8*)
definition call_FFI  :: " 'ffi ffi_state \<Rightarrow> string \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow> 'ffi ffi_state*(8 word)list "  where 
     " call_FFI st s conf bytes = (
  if ((final_event   st) = None) \<and> \<not> (s = ('''')) then
    (case (oracle0   st) s(ffi_state   st) conf bytes of
      Oracle_return ffi' bytes' =>
        if List.length bytes' = List.length bytes then
          (( st (| ffi_state := ffi'
                    , io_events :=                        
((io_events   st) @
                          [IO_event s conf (zipSameLength bytes bytes')])
            |)), bytes')
        else (( st (| final_event := (Some (Final_event s conf bytes FFI_failed)) |)), bytes)
    | Oracle_diverge =>
          (( st (| final_event := (Some (Final_event s conf bytes FFI_diverged)) |)), bytes)
    | Oracle_fail =>
        (( st (| final_event := (Some (Final_event s conf bytes FFI_failed)) |)), bytes)
    )
  else (st, bytes))"


datatype outcome = Success | Resource_limit_hit | FFI_outcome " final_event "

(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)
datatype  behaviour =
    (* There cannot be any non-returning FFI calls in a diverging
       exeuction. The list of I/O events can be finite or infinite,
       hence the llist (lazy list) type. *)
    Diverge "  io_event llist "
    (* Terminating executions can only perform a finite number of
       FFI calls. The execution can be terminated by a non-returning
       FFI call. *)
  | Terminate " outcome " " io_event list "
    (* Failure is a behaviour which we prove cannot occur for any
       well-typed program. *)
  | Fail

(* trace-based semantics can be recovered as an instance of oracle-based
 * semantics as follows. *)

(*val trace_oracle : oracle (llist io_event)*)
definition trace_oracle  :: " string \<Rightarrow>(io_event)llist \<Rightarrow>(8 word)list \<Rightarrow>(8 word)list \<Rightarrow>((io_event)llist)oracle_result "  where 
     " trace_oracle s io_trace conf input1 = (
  (case  lhd' io_trace of
    Some (IO_event s' conf' bytes2) =>
      if (s = s') \<and> ((List.map fst bytes2 = input1) \<and> (conf = conf')) then
        Oracle_return (Option.the (ltl' io_trace)) (List.map snd bytes2)
      else Oracle_fail
  | _ => Oracle_fail
  ))"

end
