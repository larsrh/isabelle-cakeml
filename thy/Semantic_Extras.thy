theory Semantic_Extras
imports
  CakeML.BigStep
  CakeML.SemanticPrimitivesAuxiliary
  CakeML.AstAuxiliary
  "HOL-Library.Simps_Case_Conv"
begin

hide_const (open) sem_env.v

code_pred
  (modes: evaluate: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as compute
      and evaluate_list: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool
      and evaluate_match: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate .

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

end

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

context begin

private fun_cases do_opappE: "do_opapp vs = Some res"

lemma do_opapp_cases:
  assumes "do_opapp vs = Some (env', exp')"
  obtains (closure) env n v0
            where "vs = [Closure env n exp', v0]"
                  "env' = (env \<lparr> sem_env.v := nsBind n v0 (sem_env.v env) \<rparr> )"
        | (recclosure) env funs name n v0
            where "vs = [Recclosure env funs name, v0]"
              and "allDistinct (map (\<lambda>(f, _, _). f) funs)"
              and "find_recfun name funs = Some (n, exp')"
              and "env' = (env \<lparr> sem_env.v := nsBind n v0 (build_rec_env funs env (sem_env.v env)) \<rparr> )"
proof -
  show thesis
    using assms
    apply (rule do_opappE)
    apply (rule closure; auto)
    apply (auto split: if_splits option.splits)
    apply (rule recclosure)
    apply auto
    done
qed

end

end