theory Big_Step_Total
imports Semantic_Extras
begin

lemma evaluate_list_total:
  fixes s :: "'a state"
  assumes "\<And>e env s::'a state. e \<in> set es \<Longrightarrow> \<exists>s' r. evaluate True env s e (s', r)"
  shows "\<exists>s' r. evaluate_list True env s es (s', r)"
using assms proof (induction es arbitrary: env s)
  case Nil
  then show ?case by (metis evaluate_match_evaluate_list_evaluate.empty)
next
  case (Cons e es)
  then obtain s' r where e: "evaluate True env s e (s', r)"
    by fastforce

  show ?case
    proof (cases r)
      case (Rval v)

      have "\<exists>s'' r. evaluate_list True env s' es (s'', r)"
        using Cons by auto
      then obtain s'' r where "evaluate_list True env s' es (s'', r)"
        by auto

      with e Rval show ?thesis
        by (cases r)
           (metis evaluate_match_evaluate_list_evaluate.cons1 evaluate_match_evaluate_list_evaluate.cons3)+
    next
      case Rerr
      with e show ?thesis by (metis evaluate_match_evaluate_list_evaluate.cons2)
    qed
qed

lemma evaluate_match_total:
  fixes s :: "'a state"
  assumes "\<And>p e env s::'a state. (p, e) \<in> set pes \<Longrightarrow> \<exists>s' r. evaluate True env s e (s', r)"
  shows "\<exists>s' r. evaluate_match True env s v pes v' (s', r)"
using assms proof (induction pes arbitrary: env s)
  case Nil
  then show ?case by (metis mat_empty)
next
  case (Cons pe pes)
  then obtain p e where "pe = (p, e)" by force

  show ?case
    proof (cases "allDistinct (pat_bindings p [])")
      case distinct: True
      show ?thesis
        proof (cases "pmatch (c env) (refs s) p v []")
          case No_match

          have "\<exists>s' r. evaluate_match True env s v pes v' (s', r)"
            apply (rule Cons)
            apply (rule Cons)
            by auto
          then obtain s' r where "evaluate_match True env s v pes v' (s', r)"
            by auto

          show ?thesis
            unfolding \<open>pe = _\<close>
            apply (intro exI)
            apply (rule mat_cons2)
            apply safe
            by fact+
        next
          case Match_type_error
          then show ?thesis
            unfolding \<open>pe = _\<close> by (metis mat_cons3)
        next
          case (Match env')

          have "\<exists>s' r. evaluate True (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>) s e (s', r)"
            apply (rule Cons)
            unfolding \<open>pe = _\<close> by auto
          then obtain s' r where "evaluate True (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>) s e (s', r)"
            by auto

          show ?thesis
            unfolding \<open>pe = _\<close>
            apply (intro exI)
            apply (rule mat_cons1)
            apply safe
            apply fact+
            done
        qed
    next
      case False
      then show ?thesis
        unfolding \<open>pe = _\<close> by (metis mat_cons4)
    qed
qed

axiomatization where
  evaluate_total: "\<exists>s' r. evaluate True env s e (s', r)" for s :: "'a state"

end