theory Big_Step_Fun_Equiv
imports
  Big_Step_Determ
  Big_Step_Total
  Evaluate_Clock
begin

locale eval =
  fixes
    eval :: "v sem_env \<Rightarrow> exp \<Rightarrow> 'a state \<Rightarrow> 'a state \<times> (v, v) result" and
    eval_list :: "v sem_env \<Rightarrow> exp list \<Rightarrow> 'a state \<Rightarrow> 'a state \<times> (v list, v) result" and
    eval_match :: "v sem_env \<Rightarrow> v \<Rightarrow> (pat \<times> exp) list \<Rightarrow> v \<Rightarrow> 'a state \<Rightarrow> 'a state \<times> (v, v) result"

  assumes
    eval: "evaluate True env s e (eval env e s)" and
    eval_list: "evaluate_list True env s es (eval_list env es s)" and
    eval_match: "evaluate_match True env s v pes err_v (eval_match env v pes err_v s)"
begin

lemmas eval_all = eval eval_list eval_match

end

lemma run_eval: "\<exists>run_eval. \<forall>env e s. evaluate True env s e (run_eval env e s)"
proof -
  define f where "f env_e_s = (case env_e_s of (env, e, s::'a state) \<Rightarrow> evaluate True env s e)" for env_e_s
  have "\<exists>g. \<forall>env_e_s. f env_e_s (g env_e_s)"
    proof (rule choice, safe, unfold f_def prod.case)
      fix env e
      fix s :: "'a state"
      obtain s' r where "evaluate True env s e (s', r)"
        by (metis evaluate_total)
      then show "\<exists>r. evaluate True env s e r"
        by auto
    qed
  then show ?thesis
    unfolding f_def
    by force
qed

lemma run_eval_list: "\<exists>run_eval_list. \<forall>env es s. evaluate_list True env s es (run_eval_list env es s)"
proof -
  define f where "f env_es_s = (case env_es_s of (env, es, s::'a state) \<Rightarrow> evaluate_list True env s es)" for env_es_s
  have "\<exists>g. \<forall>env_es_s. f env_es_s (g env_es_s)"
    proof (rule choice, safe, unfold f_def prod.case)
      fix env es
      fix s :: "'a state"
      obtain s' r where "evaluate_list True env s es (s', r)"
        by (metis evaluate_list_total)
      then show "\<exists>r. evaluate_list True env s es r"
        by auto
    qed
  then show ?thesis
    unfolding f_def
    by force
qed

lemma run_eval_match: "\<exists>run_eval_match. \<forall>env v pes err_v s. evaluate_match True env s v pes err_v (run_eval_match env v pes err_v s)"
proof -
  define f where "f env_v_pes_err_v_s = (case env_v_pes_err_v_s of (env, v, pes, err_v, s::'a state) \<Rightarrow> evaluate_match True env s v pes err_v)" for env_v_pes_err_v_s
  have "\<exists>g. \<forall>env_es_s. f env_es_s (g env_es_s)"
    proof (rule choice, safe, unfold f_def prod.case)
      fix env v pes err_v
      fix s :: "'a state"
      obtain s' r where "evaluate_match True env s v pes err_v (s', r)"
        by (metis evaluate_match_total)
      then show "\<exists>r. evaluate_match True env s v pes err_v r"
        by auto
    qed
  then show ?thesis
    unfolding f_def
    by force
qed

global_interpretation run: eval
  "SOME f. \<forall>env e s. evaluate True env s e (f env e s)"
  "SOME f. \<forall>env es s. evaluate_list True env s es (f env es s)"
  "SOME f. \<forall>env v pes err_v s. evaluate_match True env s v pes err_v (f env v pes err_v s)"
  defines
    run_eval = "SOME f. \<forall>env e s. evaluate True env s e (f env e s)" and
    run_eval_list = "SOME f. \<forall>env es s. evaluate_list True env s es (f env es s)" and
    run_eval_match = "SOME f. \<forall>env v pes err_v s. evaluate_match True env s v pes err_v (f env v pes err_v s)"
proof (standard, goal_cases)
  case 1
  show ?case
    using someI_ex[OF run_eval, rule_format] .
next
  case 2
  show ?case
    using someI_ex[OF run_eval_list, rule_format] .
next
  case 3
  show ?case
    using someI_ex[OF run_eval_match, rule_format] .
qed

hide_fact run_eval
hide_fact run_eval_list
hide_fact run_eval_match

lemma evaluate_iff:
  "evaluate True env st e r \<longleftrightarrow> (run_eval env e st = r)"
  "evaluate_list True env st es r' \<longleftrightarrow> (run_eval_list env es st = r')"
  "evaluate_match True env st v pes v' r'' \<longleftrightarrow> (run_eval_match env v pes v' st = r'')"
by (metis run.eval_all evaluate_determ)+

end