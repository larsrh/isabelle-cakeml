section "Lemmas about the clocked semantics"

theory Big_Step_Clocked
  imports
    Semantic_Extras
    Big_Step_Total
    Big_Step_Determ
begin

\<comment>\<open>From HOL4 bigClockScript.sml\<close>

lemma do_app_no_runtime_error:
  assumes "do_app (refs s, ffi s) op0 (rev vs) = Some ((refs', ffi'), res)"
  shows "res \<noteq> Rerr (Rabort Rtimeout_error)"
using assms
apply (auto
        split: op0.splits list.splits v.splits lit.splits if_splits word_size.splits
               eq_result.splits option.splits store_v.splits
        simp: store_alloc_def store_assign_def call_FFI_def Let_def)
by (auto split: oracle_result.splits option.splits if_splits)

context
  notes do_app.simps[simp del]
begin

private lemma big_unclocked0:
  "evaluate_match ck env s v pes err_v r1 \<Longrightarrow> ck = False \<Longrightarrow> snd r1 \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock s) = (clock (fst r1))"
  "evaluate_list ck env s es r2 \<Longrightarrow> ck = False \<Longrightarrow> snd r2 \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock s) = (clock (fst r2))"
  "evaluate ck env s e r3 \<Longrightarrow> ck = False \<Longrightarrow> snd r3 \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock s) = (clock (fst r3))"
  by (induction rule: evaluate_match_evaluate_list_evaluate.inducts)
     (auto intro!: do_app_no_runtime_error)

corollary big_unclocked_notimeout:
  "evaluate_match False env s v pes err_v (s', r1) \<Longrightarrow> r1 \<noteq> Rerr (Rabort Rtimeout_error)"
  "evaluate_list False env s es (s', r2) \<Longrightarrow> r2 \<noteq> Rerr (Rabort Rtimeout_error)"
  "evaluate False env s e (s', r3) \<Longrightarrow> r3 \<noteq> Rerr (Rabort Rtimeout_error)"
using big_unclocked0 by fastforce+

corollary big_unclocked_unchanged:
  "evaluate_match False env s v pes err_v (s', r1) \<Longrightarrow> clock s = clock s'"
  "evaluate_list False env s es (s', r2) \<Longrightarrow> clock s = clock s'"
  "evaluate False env s e (s', r3) \<Longrightarrow> clock s = clock s'"
using big_unclocked0 by fastforce+

private lemma big_unclocked1:
 "evaluate_match ck env s v pes err_v r1 \<Longrightarrow> \<forall>st' r. r1 = (st', r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error)
  \<longrightarrow> evaluate_match False env (s \<lparr> clock := cnt \<rparr>) v pes err_v ((st' \<lparr> clock := cnt \<rparr>), r)"
 "evaluate_list ck env s es r2 \<Longrightarrow> \<forall>st' r. r2 = (st', r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error)
  \<longrightarrow> evaluate_list False env (s \<lparr> clock := cnt \<rparr>) es ((st' \<lparr> clock := cnt \<rparr>), r)"
 "evaluate ck env s e r3 \<Longrightarrow> \<forall>st' r. r3 = (st', r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error)
 \<longrightarrow> evaluate False env (s \<lparr> clock := cnt \<rparr>) e ((st' \<lparr> clock := cnt \<rparr>), r)"
by (induction arbitrary: cnt and cnt and cnt rule: evaluate_match_evaluate_list_evaluate.inducts)
   (auto intro: evaluate_match_evaluate_list_evaluate.intros split:if_splits)

lemma big_unclocked_ignore:
 "evaluate_match ck env s v pes err_v (st', r1) \<Longrightarrow> r1 \<noteq> Rerr (Rabort Rtimeout_error) \<Longrightarrow>
    evaluate_match False env (s \<lparr> clock := cnt \<rparr>) v pes err_v (st' \<lparr> clock := cnt \<rparr>, r1)"
 "evaluate_list ck env s es (st', r2) \<Longrightarrow> r2 \<noteq> Rerr (Rabort Rtimeout_error) \<Longrightarrow>
    evaluate_list False env (s \<lparr> clock := cnt \<rparr>) es (st' \<lparr> clock := cnt \<rparr>, r2)"
 "evaluate ck env s e (st', r3) \<Longrightarrow> r3 \<noteq> Rerr (Rabort Rtimeout_error) \<Longrightarrow>
    evaluate False env (s \<lparr> clock := cnt \<rparr>) e (st' \<lparr> clock := cnt \<rparr>, r3)"
by (rule big_unclocked1[rule_format]; (assumption | simp))+

lemma big_unclocked:
  assumes "evaluate False env s e (s',r) \<Longrightarrow> r \<noteq> Rerr (Rabort Rtimeout_error)"
  assumes "evaluate False env s e (s',r) \<Longrightarrow> clock s = clock s'"
  assumes "evaluate False env (s \<lparr> clock := count1 \<rparr>) e ((s' \<lparr> clock := count1 \<rparr>),r)"
  shows "evaluate False env (s \<lparr> clock := count2 \<rparr>) e ((s' \<lparr> clock := count2 \<rparr>),r)"
using assms big_unclocked0(3) big_unclocked_ignore(3) by fastforce

private lemma add_to_counter0:
  "evaluate_match ck env s v pes err_v r1 \<Longrightarrow> \<forall>s' r' extra. (r1 = (s',r')) \<and> (r' \<noteq> Rerr (Rabort Rtimeout_error)) \<and> (ck = True)
   \<longrightarrow> evaluate_match True env (s \<lparr> clock := (clock   s)+extra \<rparr>) v pes err_v ((s' \<lparr> clock := (clock   s')+ extra\<rparr>),r')"
  "evaluate_list ck env s es r2 \<Longrightarrow>  \<forall>s' r' extra. (r2 = (s',r')) \<and> (r' \<noteq> Rerr (Rabort Rtimeout_error)) \<and> (ck = True)
   \<longrightarrow> evaluate_list True env (s \<lparr> clock := (clock   s)+extra \<rparr>) es ((s' \<lparr> clock := (clock   s')+ extra\<rparr>),r')"
  "evaluate ck env s e r3 \<Longrightarrow> \<forall>s' r' extra. (r3 = (s',r')) \<and> (r' \<noteq> Rerr (Rabort Rtimeout_error)) \<and> (ck = True)
   \<longrightarrow> evaluate True env (s \<lparr> clock := (clock   s)+extra \<rparr>) e ((s' \<lparr> clock := (clock   s')+ extra\<rparr>),r')"
by (induction rule: evaluate_match_evaluate_list_evaluate.inducts)
   (auto intro: evaluate_match_evaluate_list_evaluate.intros)

corollary add_to_counter:
  "evaluate_match True env s v pes err_v (s', r1) \<Longrightarrow> r1 \<noteq> Rerr (Rabort Rtimeout_error) \<Longrightarrow>
     evaluate_match True env (s \<lparr> clock := clock s + extra \<rparr>) v pes err_v ((s' \<lparr> clock := clock s' + extra \<rparr>), r1)"
  "evaluate_list True env s es (s', r2) \<Longrightarrow> r2 \<noteq> Rerr (Rabort Rtimeout_error) \<Longrightarrow>
     evaluate_list True env (s \<lparr> clock := (clock   s)+extra \<rparr>) es ((s' \<lparr> clock := (clock   s')+ extra\<rparr>),r2)"
  "evaluate True env s e (s', r3) \<Longrightarrow> r3 \<noteq> Rerr (Rabort Rtimeout_error) \<Longrightarrow>
     evaluate True env (s \<lparr> clock := (clock   s)+extra \<rparr>) e ((s' \<lparr> clock := (clock s')+ extra\<rparr>),r3)"
by (rule add_to_counter0[rule_format]; (assumption | simp))+

lemma add_clock:
  "evaluate_match ck env s v pes err_v r1 \<Longrightarrow> \<forall>s' r'. (r1 = (s', r') \<and> ck = False
   \<longrightarrow> (\<exists>c. evaluate_match True env (s (| clock := c |)) v pes err_v ((s' (| clock := 0 |)),r')))"
  "evaluate_list ck env s es r2 \<Longrightarrow> \<forall>s' r'. (r2 = (s', r') \<and> ck = False
   \<longrightarrow> (\<exists>c. evaluate_list True env (s (| clock := c |)) es ((s' (| clock := 0 |)),r')))"
  "evaluate ck env s e r3 \<Longrightarrow> \<forall>s' r'. (r3 = (s', r') \<and> ck = False
   \<longrightarrow> (\<exists>c. evaluate True env (s (| clock := c |)) e ((s' (| clock := 0 |)),r')))"
proof (induction rule:evaluate_match_evaluate_list_evaluate.inducts)
  case app1
  then show ?case
    apply clarsimp
    subgoal for s' r' c c'
      apply (drule add_to_counter(2)[where extra = "c'+1"])
      by (auto intro!: evaluate_match_evaluate_list_evaluate.intros)
    done
qed (force intro: evaluate_match_evaluate_list_evaluate.intros dest:add_to_counter(3))+

lemma clock_monotone:
  "evaluate_match ck env s v pes err_v r1 \<Longrightarrow> \<forall>s' r'. r1 = (s',r') \<and> (ck=True) \<longrightarrow> (clock   s') \<le> (clock   s)"
  "evaluate_list ck env s es r2 \<Longrightarrow> \<forall>s' r'. r2 = (s',r') \<and> (ck = True) \<longrightarrow> (clock   s') \<le> (clock   s)"
  "evaluate ck env s e r3 \<Longrightarrow> \<forall>s' r'. r3 = (s',r') \<and> (ck = True) \<longrightarrow> (clock   s') \<le> (clock   s)"
  by (induction rule:evaluate_match_evaluate_list_evaluate.inducts) auto

lemma big_clocked_unclocked_equiv:
  "evaluate False env s e (s',r1) =
   (\<exists>c. evaluate True env (s (| clock := c |)) e ((s' (| clock := 0 |)),r1) \<and>
        r1 \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock   s) = (clock   s'))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using big_unclocked_unchanged(3) by (fastforce simp add: big_unclocked_unchanged big_unclocked_notimeout add_clock)
next
  assume ?rhs
  then show ?lhs
    apply -
    apply (elim conjE exE)
    apply (drule big_unclocked_ignore(3))
     apply auto
    by (metis big_unclocked state.record_simps(7))
qed

lemma big_clocked_timeout_0:
  "evaluate_match ck env s v pes err_v r1  \<Longrightarrow> \<forall>s'. r1 = (s',Rerr (Rabort Rtimeout_error)) \<and> ck = True \<longrightarrow> (clock s') = 0"
  "evaluate_list ck env s es r2  \<Longrightarrow> \<forall>s'. r2 = (s',Rerr (Rabort Rtimeout_error)) \<and> ck = True \<longrightarrow> (clock s') = 0"
  "evaluate ck env s e r3  \<Longrightarrow> \<forall>s'. r3 = (s',Rerr (Rabort Rtimeout_error)) \<and> ck = True \<longrightarrow> (clock s') = 0"
proof(induction rule:evaluate_match_evaluate_list_evaluate.inducts)
  case app4
  then show ?case by (auto dest!:do_app_no_runtime_error)
qed(auto)

lemma big_clocked_unclocked_equiv_timeout:
  "(\<forall>r. \<not>evaluate False env s e r) =
   (\<forall>c. \<exists>s'. evaluate True env (s \<lparr> clock := c \<rparr>) e (s',Rerr (Rabort Rtimeout_error)) \<and> (clock s') = 0)" (is "?lhs = ?rhs")
proof rule
  assume l:?lhs
  show ?rhs
  proof
    fix c
    obtain s' r where e:"evaluate True env (update_clock (\<lambda>_. c) s) e (s',r)"
      using evaluate_total by blast
    have r:"r = Rerr (Rabort Rtimeout_error)"
      using l big_unclocked_ignore(3)[OF e, simplified]
      by (metis state.record_simps(7))
    moreover have "(clock s') = 0"
      using r e big_clocked_timeout_0(3) by blast
    ultimately show "\<exists>s'. evaluate True env (update_clock (\<lambda>_. c) s) e (s', Rerr (Rabort Rtimeout_error)) \<and> clock s' = 0"
      using e by blast
  qed
next
  assume ?rhs
  then show ?lhs
    by (metis big_clocked_unclocked_equiv eq_snd_iff evaluate_determ(3))
qed

lemma sub_from_counter:
  "evaluate_match ck env s v pes err_v r1 \<Longrightarrow>
   \<forall>count count' s' r'.
    (clock   s) = count + extra1 \<and>
    r1 = (s',r') \<and>
    (clock   s') = count' + extra1 \<and>
    ck = True \<longrightarrow>
    evaluate_match True env (s (| clock := count |)) v pes err_v ((s' (| clock := count' |) ),r')"
  "evaluate_list ck env s es r2 \<Longrightarrow>
   \<forall>count count' s' r'.
    (clock   s) = count + extra2 \<and>
    r2 = (s',r') \<and>
    (clock   s') = count' + extra2 \<and>
    ck = True \<longrightarrow>
    evaluate_list True env (s (| clock := count |)) es ((s' (| clock := count' |) ),r')"
  "evaluate ck env s e r3 \<Longrightarrow>
   \<forall>count count' s' r'.
    (clock   s) = count + extra3 \<and>
    r3 = (s',r') \<and>
    (clock   s') = count' + extra3 \<and>
    ck = True \<longrightarrow>
    evaluate True env (s (| clock := count |)) e ((s' (| clock := count' |) ),r')"
proof (induction arbitrary:extra1 and extra2 and extra3 rule:evaluate_match_evaluate_list_evaluate.inducts)
  case (handle2 ck s1 s2 env e pes v1 bv)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2) \<ge> extra3")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra3" in spec)
     apply rule
     apply force
    by (auto dest:clock_monotone(1))
next
  case (app1 ck env es vs env' e bv s1 s2)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)-1\<ge>extra3")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra3-1" in spec)
     apply rule
     apply force
    by (auto dest:clock_monotone(3))
next
  case (log1 ck env op0 e1 e2 v1 e' bv s1 s2)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)\<ge>extra3")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra3" in spec)
     apply rule
     apply force
    by (auto dest:clock_monotone(3))
next
  case (if1 ck env e1 e2 e3 v1 e' bv s1 s2)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)\<ge>extra3")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra3" in spec)
     apply rule
     apply force
    by (auto intro: evaluate_match_evaluate_list_evaluate.intros dest:clock_monotone(3))
next
  case (mat1 ck env e pes v1 bv s1 s2)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)\<ge>extra3")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra3" in spec)
     apply rule
     apply force
    by (auto dest:clock_monotone(1))
next
  case (let1 ck env n e1 e2 v1 bv s1 s2)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)\<ge>extra3")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra3" in spec)
     apply rule
    apply force
    by (auto dest:clock_monotone(3))
next
  case (cons1 ck env e es v1 vs s1 s2 s3)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)\<ge>extra2")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra2" in spec)
     apply rule
     apply force
    by (auto dest:clock_monotone(2))
next
  case (cons3 ck env e es v1 err s1 s2 s3)
  then show ?case
    apply clarsimp
    apply (subgoal_tac "(clock   s2)\<ge>extra2")
     apply (drule spec)
     apply (drule spec)
     apply (drule spec)
     apply (drule_tac x="(clock   s2)-extra2" in spec)
     apply rule
     apply force
    by (auto dest:clock_monotone(2))
qed(fastforce intro:evaluate_match_evaluate_list_evaluate.intros)+

lemma clocked_min_counter:
  assumes "evaluate True env s e (s',r')"
  shows "evaluate True env (s (| clock := (clock   s) - (clock   s') |)) e ((s' (| clock := 0 |)),r')"
proof -
  from assms have "(clock   s) \<ge> (clock   s')"
    by (fastforce intro:clock_monotone(3)[rule_format])
  then show ?thesis
    thm sub_from_counter(3)[rule_format]
    using assms by (auto intro!:sub_from_counter(3)[rule_format])
qed

(* FIXME dec *)

(*
lemma dec_evaluate_not_timeout:
  "evaluate_dec False mn env s d (s',r) \<Longrightarrow> r \<noteq> Rerr (Rabort Rtimeout_error)"
  by (ind_cases "evaluate_dec False mn env s d (s', r)", auto dest: big_unclocked_notimeout)

lemma dec_unclocked_ignore:
  "evaluate_dec ck mn env s d res \<Longrightarrow>
   \<forall>s' r count. res = (s',r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error) \<longrightarrow>
    evaluate_dec False mn env (s (| clock := count |)) d (s' (| clock := count |),r)"
proof (induction rule:evaluate_dec.inducts)
  case dtype1
  then show ?case
    apply auto
    using evaluate_dec.intros state.record_simps(4)
    by metis
next
  case dexn1
  then show ?case
    apply auto
    using evaluate_dec.intros state.record_simps(4)
    by (metis Un_insert_left sup_bot.left_neutral)
qed (force intro:evaluate_dec.intros simp add:big_unclocked_ignore(3))+

private lemma dec_unclocked_1:
  assumes "evaluate_dec False mn env s d (s',r)"
  shows "(r \<noteq> Rerr (Rabort Rtimeout_error)) \<and> (clock   s) = (clock   s')"
using assms by cases (auto dest: big_unclocked_notimeout big_unclocked_unchanged)

private lemma dec_unclocked_2:
  assumes "evaluate_dec False mn env (s \<lparr> clock := count1 \<rparr>) d ((s' \<lparr> clock := count1 \<rparr>),r)"
  shows "evaluate_dec False mn env (s \<lparr> clock := count2 \<rparr>) d ((s' \<lparr> clock := count2 \<rparr>),r)"
proof -
  from assms have "r \<noteq> Rerr (Rabort Rtimeout_error)"
    using dec_evaluate_not_timeout by blast
  then show ?thesis
    using assms dec_unclocked_ignore[rule_format]
    by fastforce
qed

lemma dec_unclocked:
  "(evaluate_dec False mn env s d (s',r) \<longrightarrow> (r \<noteq> Rerr (Rabort Rtimeout_error)) \<and> (clock   s) = (clock   s')) \<and>
   (evaluate_dec False mn env (s (| clock := count1 |)) d ((s' (| clock := count1 |)),r) \<longrightarrow>
   evaluate_dec False mn env (s (| clock := count2 |)) d ((s' (| clock := count2 |)),r))"
  using dec_unclocked_1 dec_unclocked_2 by blast
*)
corollary big_clocked_unclocked_equiv_timeout_1:
  "(\<forall>r. \<not> evaluate False env s e r) \<Longrightarrow>
  (\<forall>c. \<exists>s'. evaluate True env (update_clock (\<lambda>_. c) s) e (s', Rerr (Rabort Rtimeout_error)) \<and> clock s' = 0)"
  using big_clocked_unclocked_equiv_timeout by blast
(*
lemma not_evaluate_dec_timeout:
  assumes "\<forall>r. \<not>evaluate_dec False mn env s d r"
  shows "\<exists>r. evaluate_dec True mn env s d r \<and> snd r = Rerr (Rabort Rtimeout_error)"
proof (cases d)
  case (Dlet locs p e)
  have "\<not> evaluate False env s e r" for r
    apply rule
    apply (cases "Lem_list.allDistinct (pat_bindings p [])")
    subgoal
      apply (cases r)
      apply hypsubst_thin
      subgoal for s' r
        apply (cases r; hypsubst_thin)
        subgoal for v
          apply (cases "pmatch(c   env)(refs   s') p v []")
          using assms unfolding Dlet by (metis evaluate_dec.intros)+
        subgoal
          using assms unfolding Dlet by (metis dlet5)
        done
      done
    subgoal
      using assms unfolding Dlet by (metis dlet4)
    done
  note big_clocked_unclocked_equiv_timeout_1[rule_format, OF this]
  then obtain s' where "evaluate True env (update_clock (\<lambda>_. clock s) s) e (s', Rerr (Rabort Rtimeout_error))"
    by blast
  then have "evaluate True env s e (s', Rerr (Rabort Rtimeout_error))"
    by simp

  have "Lem_list.allDistinct (pat_bindings p [])"
    apply (rule ccontr)
    apply (drule dlet4)
    using assms Dlet by blast

  show ?thesis
    unfolding Dlet
    apply (intro exI conjI)
     apply (rule dlet5)
     apply rule
      apply fact+
    apply simp
    done
qed (metis evaluate_dec.intros assms)+

lemma dec_clocked_total: "\<exists>res. evaluate_dec True mn env s d res"
proof (cases d)
  case (Dlet locs p e)
  obtain s' r where e:"evaluate True env s e (s', r)" by (metis evaluate_total)
  show ?thesis
    unfolding Dlet
    apply (cases "Lem_list.allDistinct (pat_bindings p [])")
    subgoal
      using e apply (cases r)
      subgoal for v
        apply hypsubst_thin
        apply (cases "pmatch(c   env)(refs   s') p v []")
        using evaluate_dec.intros by metis+
      using evaluate_dec.intros by metis
    using evaluate_dec.intros by metis
qed (blast intro: evaluate_dec.intros)+

lemma dec_clocked_min_counter:
  "evaluate_dec ck mn env s d res \<Longrightarrow> ck = True \<Longrightarrow>
   evaluate_dec ck mn env (s (| clock := (clock   s) - (clock   (fst res))|)) d (((fst res) (| clock := 0|)), snd res)"
proof (induction rule:evaluate_dec.inducts)
next
  case dtype1
  then show ?case
    apply auto
    using state.record_simps(4) evaluate_dec.intros
    by metis
next
  case dexn1
  then show ?case
    apply auto
    using evaluate_dec.intros state.record_simps(4)
    by (metis Un_insert_left sup_bot.left_neutral)
qed (force intro:evaluate_dec.intros simp add:clocked_min_counter)+

lemma dec_sub_from_counter:
  "evaluate_dec ck mn env s d res \<Longrightarrow>
   (\<forall>count count' s' r. (clock   s) = count + extra \<and> (clock   s') = count' + extra \<and> res = (s',r) \<and> ck = True \<longrightarrow>
     evaluate_dec ck mn env (s (| clock := count |)) d ((s' (| clock := count' |)),r))"
proof (induction rule:evaluate_dec.inducts)
next
  case dtype1
  then show ?case
    apply auto
    using evaluate_dec.intros state.record_simps(4)
    by (metis)
next
  case dtype2
  then show ?case
    apply rule
    by (auto intro!: evaluate_dec.intros)
next
  case dexn1
  then show ?case
    apply (auto)
    using evaluate_dec.intros state.record_simps(4)
    by (metis Un_insert_left sup_bot.left_neutral)
qed (force intro:evaluate_dec.intros simp add:sub_from_counter)+

lemma dec_clock_monotone:
  "evaluate_dec ck mn env s d res \<Longrightarrow> ck = True \<Longrightarrow> (clock   (fst res)) \<le> (clock   s)"
  by (induction rule:evaluate_dec.inducts)
     (auto simp add:clock_monotone)

lemma dec_add_clock:
  "evaluate_dec ck mn env s d res \<Longrightarrow>
   \<forall>s' r. res = (s',r) \<and> ck = False \<longrightarrow> (\<exists>c. evaluate_dec True mn env (s (| clock := c |)) d ((s' (| clock := 0 |)),r))"
proof (induction rule: evaluate_dec.inducts)
case dlet1
  then show ?case
    apply rule
    apply (drule add_clock(3))
    by (auto|rule)+
next
  case dlet2
  then show ?case
    apply rule
    apply (drule add_clock(3))
    apply auto
    by rule+ auto
next
  case dlet3
  then show ?case
    apply rule
    apply (drule add_clock(3))
    apply auto
    by rule+ auto
next
  case dlet4
  then show ?case
    by (auto intro:evaluate_dec.intros)
next
  case dlet5
  then show ?case
    apply rule
    apply (drule add_clock(3))
    apply auto
    by rule+ auto
next
  case dletrec1
  then show ?case
    apply auto
    by rule+ auto
next
  case dletrec2
  then show ?case
    apply auto
    by rule+ auto
next
  case dtype1
  then show ?case
    apply auto
    by (metis (full_types) evaluate_dec.dtype1 state.record_simps(4))
next
  case dtype2
  then show ?case
    apply clarsimp
    by rule+ auto
next
  case dtabbrev
  then show ?case
    apply auto
    by rule+
next
  case dexn1
  then show ?case
    apply auto
    apply (rule exI[where x=0])
    using evaluate_dec.intros state.record_simps(4)
    by (metis Un_insert_left sup_bot.left_neutral)
next
case dexn2
  then show ?case
    apply auto
    apply rule
    apply rule
    by auto
qed

lemma dec_add_to_counter:
  "evaluate_dec ck mn env s d res \<Longrightarrow>
   \<forall>s' r extra. res = (s',r) \<and> ck = True \<and> r \<noteq> Rerr (Rabort Rtimeout_error) \<longrightarrow>
     evaluate_dec True mn env (s (| clock := (clock   s) + extra |)) d ((s' (| clock := (clock   s') + extra |)),r)"
proof (induction rule:evaluate_dec.inducts)
next
  case dtype1
  then show ?case
    apply auto
    using evaluate_dec.intros state.record_simps(4)
    by (metis)
next
  case dexn1
  then show ?case
    apply auto
    using evaluate_dec.intros state.record_simps(4)
    by (metis Un_insert_left sup_bot.left_neutral)
qed (force intro:evaluate_dec.intros simp add:add_to_counter(3))+

lemma dec_unclocked_unchanged:
  "evaluate_dec ck mn env s d r \<Longrightarrow> ck = False \<Longrightarrow> (snd r) \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock   s) = (clock   (fst r))"
  by (induction rule: evaluate_dec.inducts)
     (auto simp: big_unclocked_notimeout big_clocked_unclocked_equiv)

lemma dec_clocked_unclocked_equiv:
  "evaluate_dec False mn env s1 d (s2,r) =
  (\<exists>c. evaluate_dec True mn env (s1 (| clock := c |)) d ((s2 (| clock := 0 |)),r) \<and>
       r \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock   s1) = (clock   s2))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto dest:dec_unclocked_unchanged dec_add_clock)
next
  assume ?rhs
  then show ?lhs
    using dec_unclocked_ignore
  proof -
    (* sledgehammer proof *)
    obtain nn :: nat where
      f1: "evaluate_dec True mn env (update_clock (\<lambda>n. nn) s1) d (update_clock (\<lambda>n. 0) s2, r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error) \<and> clock s1 = clock s2"
      using \<open>\<exists>c. evaluate_dec True mn env (update_clock (\<lambda>_. c) s1) d (update_clock (\<lambda>_. 0) s2, r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error) \<and> clock s1 = clock s2\<close> by blast
    then have "\<forall>n. evaluate_dec False mn env (update_clock (\<lambda>na. n) s1) d (update_clock (\<lambda>na. n) s2, r)"
      using dec_unclocked_ignore
      by fastforce
    then show ?thesis
      using f1
      by (metis (full_types) state.record_simps(7))
  qed
qed

lemma decs_add_clock:
  "evaluate_decs ck mn env s ds res \<Longrightarrow>
   \<forall>s' r. res = (s',r) \<and> ck = False \<longrightarrow> (\<exists>c. evaluate_decs True mn env (s (| clock := c |)) ds (s' (| clock := 0 |),r))"
proof (induction rule:evaluate_decs.inducts)
  case cons1
  then show ?case
    using dec_add_clock evaluate_decs.cons1 by blast
next
  case cons2
  then show ?case
    apply auto
    apply (drule dec_add_clock)
    using dec_add_to_counter[rule_format] evaluate_decs.cons2
    by fastforce
qed (auto intro:evaluate_decs.intros)

lemma decs_evaluate_not_timeout:
  "evaluate_decs ck mn env s ds r \<Longrightarrow>
   \<forall>s' r'. ck = False \<and> r = (s',r') \<longrightarrow> r' \<noteq> Rerr (Rabort Rtimeout_error)"
  by (induction rule:evaluate_decs.inducts)
     (case_tac r;fastforce dest:dec_evaluate_not_timeout)+

lemma decs_unclocked_unchanged:
  "evaluate_decs ck mn env s ds r \<Longrightarrow>
   \<forall>s' r'. ck = False \<and> r = (s',r') \<longrightarrow> r' \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock   s) = (clock   s')"
  by (induction rule:evaluate_decs.inducts)
     (case_tac r;fastforce simp add:dec_unclocked_unchanged dest:dec_evaluate_not_timeout)+

lemma decs_unclocked_ignore:
  "evaluate_decs ck mn env s d res \<Longrightarrow> \<forall>s' r count. res = (s',r) \<and> r \<noteq> Rerr (Rabort Rtimeout_error) \<longrightarrow>
    evaluate_decs False mn env (s (| clock := count |)) d ((s' (| clock := count |)),r)"
  by (induction rule:evaluate_decs.inducts)
     (auto intro!:evaluate_decs.intros simp add:dec_unclocked_ignore)

private lemma decs_unclocked_2:
  assumes "evaluate_decs False mn env (s (| clock := count1 |)) ds ((s' (| clock := count1 |)),r)"
  shows "evaluate_decs False mn env (s (| clock := count2 |)) ds ((s' (| clock := count2 |)),r)"
  using decs_unclocked_ignore[rule_format] assms decs_evaluate_not_timeout by fastforce

lemma decs_unclocked:
  "(evaluate_decs False mn env s ds (s',r) \<longrightarrow> r \<noteq> Rerr (Rabort Rtimeout_error) \<and> (clock   s) = (clock   s')) \<and>
   (evaluate_decs False mn env (s (| clock := count1 |)) ds ((s' (| clock := count1 |)),r) =
   evaluate_decs False mn env (s (| clock := count2 |)) ds ((s' (| clock := count2 |)),r))"
  by (auto simp add:decs_unclocked_unchanged decs_unclocked_2)

lemma not_evaluate_decs_timeout:
  assumes "\<forall>r. \<not>evaluate_decs False mn env s ds r"
  shows "\<exists>r. evaluate_decs True mn env s ds r \<and> (snd r) = Rerr (Rabort Rtimeout_error)"
using assms proof (induction ds arbitrary:mn env s)
  case Nil
  then show ?case
    using assms evaluate_decs.intros by blast
next
  case (Cons d ds)
  obtain s' r where d:"evaluate_dec True mn env s d (s',r)"
    using dec_clocked_total by force
  then show ?case
  proof (cases r)
    case (Rval new_env)
    have "\<not> evaluate_decs False mn (extend_dec_env new_env env) s' ds (s3, r)" for s3 r

    proof
      assume "evaluate_decs False mn (extend_dec_env new_env env) s' ds (s3, r)"
      then have "evaluate_decs False mn (extend_dec_env new_env env) (s' \<lparr>clock := (clock s)\<rparr>) ds ((s3 \<lparr>clock := (clock s)\<rparr>), r)"
        using decs_unclocked decs_unclocked_ignore by fastforce
      moreover from d have "evaluate_dec False mn env s d ((s' \<lparr>clock := (clock s)\<rparr>), Rval new_env)"
        using dec_unclocked_ignore
        unfolding Rval
        by (metis (full_types) result.distinct(1) state.record_simps(7))
      ultimately show False
        using evaluate_decs.cons2 Cons
        by blast
    qed

    then show ?thesis
      using Cons.IH[simplified] evaluate_decs.cons2 d
      unfolding Rval
      by (metis combine_dec_result.simps(1) snd_conv)
  next
    case (Rerr e)
    have "e = Rabort Rtimeout_error"

    proof (rule ccontr)
      assume "e \<noteq> Rabort Rtimeout_error"
      then obtain s' where "evaluate_dec False mn env s d (s',r)"
        using dec_unclocked_ignore[rule_format, where count="clock s"] d Rerr state.simps
        by fastforce
      thus False
        unfolding Rerr
        using Cons evaluate_decs.cons1 by blast
    qed

    then show ?thesis
      using d evaluate_decs.cons1 Rerr by fastforce
  qed
qed

lemma decs_clocked_total: "\<exists>res. evaluate_decs True mn env s ds res"
proof (induction ds arbitrary:mn env s)
  case Nil
  then show ?case by (auto intro:evaluate_decs.intros)
next
  case (Cons d ds)
  obtain s' r where d:"evaluate_dec True mn env s d (s',r)"
    using dec_clocked_total
    by force
  then obtain s'' r' where ds:"evaluate_decs True mn env s' ds (s'',r')"
    using Cons by force
  from d ds show ?case
    using evaluate_decs.intros Cons by (cases r;fastforce)+
qed

lemma decs_clock_monotone:
  "evaluate_decs ck mn env s d res \<Longrightarrow> ck = True \<Longrightarrow> (clock (fst res)) \<le> (clock s)"
  by (induction rule:evaluate_decs.inducts) (fastforce dest:dec_clock_monotone)+

lemma decs_sub_from_counter:
  "evaluate_decs ck mn env s d res \<Longrightarrow>
  \<forall>extra count count' s' r'.
    (clock s) = count + extra \<and> (clock s') = count' + extra \<and>
    res = (s',r') \<and> ck = True \<longrightarrow> evaluate_decs ck mn env (s \<lparr> clock := count \<rparr>) d ((s' \<lparr> clock := count' \<rparr>),r')"
proof (induction rule:evaluate_decs.inducts)
  case (cons2 ck mn s1 s2 s3 env d ds new_env r)
  then show ?case
    apply auto
    subgoal for extra
      apply (subgoal_tac "clock s2\<ge>extra")
       apply (metis dec_sub_from_counter diff_add_inverse2 eq_diff_iff evaluate_decs.cons2 le_add2)
      using decs_clock_monotone by fastforce
    done
qed (auto intro!:evaluate_decs.intros simp add:dec_sub_from_counter)

lemma decs_clocked_min_counter:
  assumes "evaluate_decs ck mn env s ds res" "ck = True"
  shows "evaluate_decs ck mn env (s \<lparr> clock := clock s - (clock (fst res))\<rparr>) ds (((fst res) \<lparr> clock := 0 \<rparr>),(snd res))"
proof -
  from assms have "clock (fst res) \<le> clock s"
    using decs_clock_monotone by fastforce
  with assms show ?thesis
    by (auto elim!: decs_sub_from_counter[rule_format])
qed

lemma decs_add_to_counter:
  "evaluate_decs ck mn env s d res \<Longrightarrow> \<forall>s' r extra. res = (s',r) \<and> ck = True \<and> r \<noteq> Rerr (Rabort Rtimeout_error) \<longrightarrow>
    evaluate_decs True mn env (s \<lparr> clock := clock s + extra \<rparr>) d ((s' \<lparr> clock := clock s' + extra \<rparr>),r)"
proof (induction rule:evaluate_decs.inducts)
  case cons2
  then show ?case
    using dec_add_to_counter evaluate_decs.cons2 by fastforce
 qed (auto intro!:evaluate_decs.intros simp add:dec_add_to_counter)
*)

lemma clocked_evaluate:
  "(\<exists>k. BigStep.evaluate True env (update_clock (\<lambda>_. k) s) e (s', r) \<and> r \<noteq>  Rerr (Rabort Rtimeout_error)) =
   (\<exists>k. BigStep.evaluate True env (update_clock (\<lambda>_. k) s) e ((update_clock (\<lambda>_. 0) s'), r) \<and> r \<noteq>  Rerr (Rabort Rtimeout_error))"
  apply auto
  apply (frule clock_monotone)
  subgoal for k
  by (force dest: sub_from_counter(3)[rule_format, where count' = 0 and count = "k - (clock s')"])
  by (force dest: add_to_counter[where extra = "clock s'"])

end