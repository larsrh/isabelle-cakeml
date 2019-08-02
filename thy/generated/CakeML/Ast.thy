chapter \<open>Generated by Lem from \<open>semantics/ast.lem\<close>.\<close>

theory "Ast" 

imports
  Main
  "HOL-Library.Datatype_Records"
  "LEM.Lem_pervasives"
  "LEM.Lem_pervasives_extra"
  "Lib"
  "Namespace"
  "FpSem"

begin 

\<comment> \<open>\<open>
  Definition of CakeML abstract syntax (AST).
\<close>\<close>

\<comment> \<open>\<open>open import Pervasives_extra\<close>\<close>
\<comment> \<open>\<open>open import Pervasives\<close>\<close>
\<comment> \<open>\<open>open import Lib\<close>\<close>
\<comment> \<open>\<open>open import Namespace\<close>\<close>
\<comment> \<open>\<open>open import FpSem\<close>\<close>

\<comment> \<open>\<open> Literal constants \<close>\<close>
datatype lit =
    IntLit " int "
  | Char " char "
  | StrLit " string "
  | Word8 " 8 word "
  | Word64 " 64 word "

\<comment> \<open>\<open> Built-in binary operations \<close>\<close>
datatype opn = Plus | Minus | Times | Divide | Modulo
datatype opb = Lt | Gt | Leq | Geq
datatype opw = Andw | Orw | Xor | Add | Sub
datatype shift = Lsl | Lsr | Asr | Ror

\<comment> \<open>\<open> Module names \<close>\<close>
type_synonym modN =" string "

\<comment> \<open>\<open> Variable names \<close>\<close>
type_synonym varN =" string "

\<comment> \<open>\<open> Constructor names (from datatype definitions) \<close>\<close>
type_synonym conN =" string "

\<comment> \<open>\<open> Type names \<close>\<close>
type_synonym typeN =" string "

\<comment> \<open>\<open> Type variable names \<close>\<close>
type_synonym tvarN =" string "

datatype word_size = W8 | W64

datatype op0 =
  \<comment> \<open>\<open> Operations on integers \<close>\<close>
    Opn " opn "
  | Opb " opb "
  \<comment> \<open>\<open> Operations on words \<close>\<close>
  | Opw " word_size " " opw "
  | Shift " word_size " " shift " " nat "
  | Equality
  \<comment> \<open>\<open> FP operations \<close>\<close>
  | FP_cmp " fp_cmp_op "
  | FP_uop " fp_uop_op "
  | FP_bop " fp_bop_op "
  | FP_top " fp_top_op "
  \<comment> \<open>\<open> Function application \<close>\<close>
  | Opapp
  \<comment> \<open>\<open> Reference operations \<close>\<close>
  | Opassign
  | Opref
  | Opderef
  \<comment> \<open>\<open> Word8Array operations \<close>\<close>
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  \<comment> \<open>\<open> Word/integer conversions \<close>\<close>
  | WordFromInt " word_size "
  | WordToInt " word_size "
  \<comment> \<open>\<open> string/bytearray conversions \<close>\<close>
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  \<comment> \<open>\<open> Char operations \<close>\<close>
  | Ord
  | Chr
  | Chopb " opb "
  \<comment> \<open>\<open> String operations \<close>\<close>
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  \<comment> \<open>\<open> Vector operations \<close>\<close>
  | VfromList
  | Vsub
  | Vlength
  \<comment> \<open>\<open> Array operations \<close>\<close>
  | Aalloc
  | AallocEmpty
  | Asub
  | Alength
  | Aupdate
  \<comment> \<open>\<open> List operations \<close>\<close>
  | ListAppend
  \<comment> \<open>\<open> Configure the GC \<close>\<close>
  | ConfigGC
  \<comment> \<open>\<open> Call a given foreign function \<close>\<close>
  | FFI " string "

\<comment> \<open>\<open> Logical operations \<close>\<close>
datatype lop =
    And
  | Or

\<comment> \<open>\<open> Types \<close>\<close>
datatype ast_t =
  \<comment> \<open>\<open> Type variables that the user writes down ('a, 'b, etc.) \<close>\<close>
    Atvar " tvarN "
  \<comment> \<open>\<open> Function type \<close>\<close>
  | Atfun " ast_t " " ast_t "
  \<comment> \<open>\<open> Tuple type \<close>\<close>
  | Attup " ast_t list "
  \<comment> \<open>\<open> Type constructor applications.
    0-ary type applications represent unparameterised types (e.g., num or string) \<close>\<close>
  | Atapp " ast_t list " " (modN, typeN) id0 "

\<comment> \<open>\<open> Patterns \<close>\<close>
datatype pat =
    Pany
  | Pvar " varN "
  | Plit " lit "
  \<comment> \<open>\<open> Constructor applications.
     A Nothing constructor indicates a tuple pattern. \<close>\<close>
  | Pcon "  ( (modN, conN)id0)option " " pat list "
  | Pref " pat "
  | Ptannot " pat " " ast_t "

\<comment> \<open>\<open> Expressions \<close>\<close>
datatype exp0 =
    Raise " exp0 "
  | Handle " exp0 " " (pat * exp0) list "
  | Lit " lit "
  \<comment> \<open>\<open> Constructor application.
     A Nothing constructor indicates a tuple pattern. \<close>\<close>
  | Con "  ( (modN, conN)id0)option " " exp0 list "
  | Var " (modN, varN) id0 "
  | Fun " varN " " exp0 "
  \<comment> \<open>\<open> Application of a primitive operator to arguments.
     Includes function application. \<close>\<close>
  | App " op0 " " exp0 list "
  \<comment> \<open>\<open> Logical operations (and, or) \<close>\<close>
  | Log " lop " " exp0 " " exp0 "
  | If " exp0 " " exp0 " " exp0 "
  \<comment> \<open>\<open> Pattern matching \<close>\<close>
  | Mat " exp0 " " (pat * exp0) list "
  \<comment> \<open>\<open> A let expression
     A Nothing value for the binding indicates that this is a
     sequencing expression, that is: (e1; e2). \<close>\<close>
  | Let "  varN option " " exp0 " " exp0 "
  \<comment> \<open>\<open> Local definition of (potentially) mutually recursive
     functions.
     The first varN is the function's name, and the second varN
     is its parameter. \<close>\<close>
  | Letrec " (varN * varN * exp0) list " " exp0 "
  | Tannot " exp0 " " ast_t "
  \<comment> \<open>\<open> Location annotated expressions, not expected in source programs \<close>\<close>
  | Lannot " exp0 " " locs "

type_synonym type_def =" ( tvarN list * typeN * (conN * ast_t list) list) list "

\<comment> \<open>\<open> Declarations \<close>\<close>
datatype dec =
  \<comment> \<open>\<open> Top-level bindings
   * The pattern allows several names to be bound at once \<close>\<close>
    Dlet " locs " " pat " " exp0 "
  \<comment> \<open>\<open> Mutually recursive function definition \<close>\<close>
  | Dletrec " locs " " (varN * varN * exp0) list "
  \<comment> \<open>\<open> Type definition
     Defines several data types, each of which has several
     named variants, which can in turn have several arguments.
   \<close>\<close>
  | Dtype " locs " " type_def "
  \<comment> \<open>\<open> Type abbreviations \<close>\<close>
  | Dtabbrev " locs " " tvarN list " " typeN " " ast_t "
  \<comment> \<open>\<open> New exceptions \<close>\<close>
  | Dexn " locs " " conN " " ast_t list "
  \<comment> \<open>\<open> Module \<close>\<close>
  | Dmod " modN " " dec list "
  \<comment> \<open>\<open> Local: local part, visible part \<close>\<close>
  | Dlocal " dec list " " dec list "

\<comment> \<open>\<open>
\<open> Specifications
   For giving the signature of a module \<close>
type spec =
  | Sval of varN * ast_t
  | Stype of type_def
  | Stabbrev of list tvarN * typeN * ast_t
  | Stype_opq of list tvarN * typeN
  | Sexn of conN * list ast_t

type specs = list spec

\<close>\<close>

\<comment> \<open>\<open> Accumulates the bindings of a pattern \<close>\<close>
\<comment> \<open>\<open>val pat_bindings : pat -> list varN -> list varN\<close>\<close>
function (sequential,domintros) 
pats_bindings  :: "(pat)list \<Rightarrow>(string)list \<Rightarrow>(string)list "  
                   and
pat_bindings  :: " pat \<Rightarrow>(string)list \<Rightarrow>(string)list "  where 
     "
pat_bindings Pany already_bound = (
  already_bound )" 
  for  already_bound  :: "(string)list "
|"
pat_bindings (Pvar n) already_bound = (
  n # already_bound )" 
  for  n  :: " string " 
  and  already_bound  :: "(string)list "
|"
pat_bindings (Plit l) already_bound = (
  already_bound )" 
  for  l  :: " lit " 
  and  already_bound  :: "(string)list "
|"
pat_bindings (Pcon _ ps) already_bound = (
  pats_bindings ps already_bound )" 
  for  ps  :: "(pat)list " 
  and  already_bound  :: "(string)list "
|"
pat_bindings (Pref p) already_bound = (
  pat_bindings p already_bound )" 
  for  p  :: " pat " 
  and  already_bound  :: "(string)list "
|"
pat_bindings (Ptannot p _) already_bound = (
  pat_bindings p already_bound )" 
  for  p  :: " pat " 
  and  already_bound  :: "(string)list "
|"
pats_bindings [] already_bound = (
  already_bound )" 
  for  already_bound  :: "(string)list "
|"
pats_bindings (p # ps) already_bound = (
  pats_bindings ps (pat_bindings p already_bound))" 
  for  ps  :: "(pat)list " 
  and  p  :: " pat " 
  and  already_bound  :: "(string)list " 
by pat_completeness auto

end
