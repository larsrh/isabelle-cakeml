chapter \<open>Generated by Lem from \<open>semantics/primTypes.lem\<close>.\<close>

theory "PrimTypes" 

imports
  Main
  "HOL-Library.Datatype_Records"
  "LEM.Lem_pervasives"
  "Lib"
  "Namespace"
  "Ast"
  "SemanticPrimitives"
  "Ffi"
  "Evaluate"
  "TypeSystem"

begin 

\<comment> \<open>\<open>
  Definition of the primitive types that are in scope before any CakeML program
  starts. Some of them are generated by running an initial program.
\<close>\<close>
\<comment> \<open>\<open>open import Pervasives\<close>\<close>
\<comment> \<open>\<open>open import Ast\<close>\<close>
\<comment> \<open>\<open>open import SemanticPrimitives\<close>\<close>
\<comment> \<open>\<open>open import Ffi\<close>\<close>
\<comment> \<open>\<open>open import Namespace\<close>\<close>
\<comment> \<open>\<open>open import Lib\<close>\<close>
\<comment> \<open>\<open>open import Evaluate\<close>\<close>

\<comment> \<open>\<open> The ordering in the following is important. The stamps generated from the
   exceptions and types must match those in semanticPrimitives \<close>\<close>
\<comment> \<open>\<open>val prim_types_program : list dec\<close>\<close>
definition prim_types_program  :: "(dec)list "  where 
     " prim_types_program = (
  [Dexn ((| row = 0, col = 0, offset = 0 |), (| row = 0, col = 0, offset = 0 |)) (''Bind'') [],
   Dexn ((| row = 0, col = 0, offset = 0 |), (| row = 0, col = 0, offset = 0 |)) (''Chr'') [],
   Dexn ((| row = 0, col = 0, offset = 0 |), (| row = 0, col = 0, offset = 0 |)) (''Div'') [],
   Dexn ((| row = 0, col = 0, offset = 0 |), (| row = 0, col = 0, offset = 0 |)) (''Subscript'') [],
   Dtype ((| row = 0, col = 0, offset = 0 |), (| row = 0, col = 0, offset = 0 |)) [([], (''bool''), [((''False''), []), ((''True''), [])])],
   Dtype ((| row = 0, col = 0, offset = 0 |), (| row = 0, col = 0, offset = 0 |)) [([([(CHR 0x27), (CHR ''a'')])], (''list''), [((''[]''), []), ((''::''), [Atvar ([(CHR 0x27), (CHR ''a'')]), Atapp [Atvar ([(CHR 0x27), (CHR ''a'')])] (Short (''list''))]) ])] ])"


\<comment> \<open>\<open>val add_to_sem_env :
  forall 'ffi. Eq 'ffi => (state 'ffi * sem_env v) -> list dec -> maybe (state 'ffi * sem_env v)\<close>\<close>
fun add_to_sem_env  :: " 'ffi state*(v)sem_env \<Rightarrow>(dec)list \<Rightarrow>('ffi state*(v)sem_env)option "  where 
     " add_to_sem_env (st, env) prog = (
  (case  fun_evaluate_decs st env prog of
    (st', Rval env') => Some (st', extend_dec_env env' env)
  | _ => None
  ))" 
  for  st  :: " 'ffi state " 
  and  env  :: "(v)sem_env " 
  and  prog  :: "(dec)list "


\<comment> \<open>\<open>val prim_sem_env : forall 'ffi. Eq 'ffi => ffi_state 'ffi -> maybe (state 'ffi * sem_env v)\<close>\<close>
definition prim_sem_env  :: " 'ffi ffi_state \<Rightarrow>('ffi state*(v)sem_env)option "  where 
     " prim_sem_env ffi1 = (
  add_to_sem_env
    ((| clock =(( 0 :: nat)), refs = ([]), ffi = ffi1, next_type_stamp =(( 0 :: nat)), next_exn_stamp =(( 0 :: nat))  |),
     (| v = nsEmpty, c = nsEmpty |))
        prim_types_program )" 
  for  ffi1  :: " 'ffi ffi_state "


\<comment> \<open>\<open>open import TypeSystem\<close>\<close>

definition prim_tenv  :: " type_env "  where 
     " prim_tenv = (
    (|
       v0 = nsEmpty, c0 = (alist_to_ns (List.rev
          [((''Bind''), ([],[],Texn_num)),
           ((''Chr''), ([],[],Texn_num)),
           ((''Div''), ([],[],Texn_num)),
           ((''Subscript''), ([],[],Texn_num)),
           ((''False''), ([],[], Tbool_num)),
           ((''True''), ([],[], Tbool_num)),
           ((''[]''), ([([(CHR 0x27), (CHR ''a'')])],[],Tlist_num)),
           ((''::''), ([([(CHR 0x27), (CHR ''a'')])],[Tvar ([(CHR 0x27), (CHR ''a'')]), Tlist (Tvar ([(CHR 0x27), (CHR ''a'')]))], Tlist_num))])),
       t = (alist_to_ns (List.rev
          [
          ((''array''),([([(CHR 0x27), (CHR ''a'')])],Tapp [Tvar ([(CHR 0x27), (CHR ''a'')])] Tarray_num)),
          ((''bool''),([],Tapp [] Tbool_num)),
          ((''char''),([],Tapp [] Tchar_num)),
          ((''exn''),([],Tapp [] Texn_num)),
          \<comment> \<open>\<open> Tfn is ->, specially handled \<close>\<close>
          ((''int''),([],Tapp [] Tint_num)),
          ((''list''),([([(CHR 0x27), (CHR ''a'')])],Tapp [Tvar ([(CHR 0x27), (CHR ''a'')])] Tlist_num)),
          ((''ref''),([([(CHR 0x27), (CHR ''a'')])],Tapp [Tvar ([(CHR 0x27), (CHR ''a'')])] Tref_num)),
          ((''string''),([],Tapp [] Tstring_num)),
          ((''unit''),([],Tapp [] Ttup_num)),
          \<comment> \<open>\<open> pairs are specially handled \<close>\<close>
          ((''vector''),([([(CHR 0x27), (CHR ''a'')])],Tapp [Tvar ([(CHR 0x27), (CHR ''a'')])] Tvector_num)),
          ((''word64''),([],Tapp [] Tword64_num)),
          ((''word8''),([],Tapp [] Tword8_num)),
          ((''word8array''),([],Tapp [] Tword8array_num))]
          )) |) )"


definition prim_type_ids  :: "(nat)set "  where 
     " prim_type_ids = ( List.set (Tlist_num # (Tbool_num # prim_type_nums)))"

end
