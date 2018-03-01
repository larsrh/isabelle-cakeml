theory Isabelle_Support
imports
  Main
  "IEEE_Floating_Point.FP64"
begin

abbreviation disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"disjoint M N \<equiv> M \<inter> N = {}"

subsection \<open>Words\<close>

consts word_lsl::"'a word \<Rightarrow> nat \<Rightarrow> 'a word"
consts word_lsr::"'a word \<Rightarrow> nat \<Rightarrow> 'a word"
consts word_asr::"'a word \<Rightarrow> nat \<Rightarrow> 'a word"
consts word_ror::"'a word \<Rightarrow> nat \<Rightarrow> 'a word"

subsection \<open>CakeML specifics\<close>

consts unknown_loc :: "'a"

end
