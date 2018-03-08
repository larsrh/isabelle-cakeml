theory Semantic_Extras
imports CakeML.BigStep "HOL-Library.Simps_Case_Conv"
begin

hide_const (open) sem_env.v

case_of_simps do_log_alt_def: do_log.simps

lemma size_list_rev[simp]: "size_list f (rev xs) = size_list f xs"
by (auto simp: size_list_conv_sum_list rev_map[symmetric])

lemma do_if_cases:
  obtains
    (none) "do_if v e1 e2 = None"
  | (true) "do_if v e1 e2 = Some e1"
  | (false) "do_if v e1 e2 = Some e2"
unfolding do_if_def
by meson

context begin

private fun_cases do_logE: "do_log op v e = res"

lemma do_log_exp: "do_log op v e = Some (Exp e') \<Longrightarrow> e = e'"
by (erule do_logE)
   (auto split: v.splits option.splits if_splits tid_or_exn.splits id0.splits list.splits)

lemma do_log_cases:
  obtains
    (none) "do_log op v e = None"
  | (val) v' where "do_log op v e = Some (Val v')"
  | (exp) "do_log op v e = Some (Exp e)"
proof (cases "do_log op v e")
  case None
  then show ?thesis using none by metis
next
  case (Some res)
  with val exp show ?thesis
    by (cases res) (metis do_log_exp)+
qed

end

code_pred
  (modes: evaluate: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as compute
      and evaluate_list: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool
      and evaluate_match: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate .

end