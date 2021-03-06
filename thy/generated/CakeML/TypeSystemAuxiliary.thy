chapter \<open>Generated by Lem from \<open>semantics/typeSystem.lem\<close>.\<close>

theory "TypeSystemAuxiliary" 

imports
  Main
  "HOL-Library.Datatype_Records"
  "LEM.Lem_pervasives_extra"
  "Lib"
  "Namespace"
  "Ast"
  "SemanticPrimitives"
  "TypeSystem"

begin 


\<comment> \<open>\<open>**************************************************\<close>\<close>
\<comment> \<open>\<open>                                                  \<close>\<close>
\<comment> \<open>\<open> Termination Proofs                               \<close>\<close>
\<comment> \<open>\<open>                                                  \<close>\<close>
\<comment> \<open>\<open>**************************************************\<close>\<close>

termination check_freevars by lexicographic_order

termination type_subst by lexicographic_order

termination deBruijn_inc by lexicographic_order

termination deBruijn_subst by lexicographic_order

termination check_type_names by lexicographic_order

termination type_name_subst by lexicographic_order

termination is_value by lexicographic_order



end
