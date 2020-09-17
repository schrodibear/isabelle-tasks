theory Bug
  imports Main
begin
definition I where "I x \<equiv> True"
ML \<open>
  structure Ctxt = Proof_Data (type T = Proof.context option fun init _ = NONE)
  fun export ctxt hyp =
    Thm.implies_intr (Thm.cterm_of ctxt hyp) #> rewrite_goals_rule ctxt [@{thm I_def}] #> curry op RS @{thm TrueI}
  fun assume_meth t _ _ (ctxt, st) =
    let
      val T = type_of t
      val hyp = Object_Logic.ensure_propT ctxt (Const (\<^const_name>\<open>I\<close>, T --> \<^typ>\<open>bool\<close>) $ t)
    in
      ctxt
      |> Ctxt.put (SOME ctxt)
      |> Proof_Context.add_assms ((export ctxt hyp, I) |> K |> K) [(Thm.no_attributes \<^binding>\<open>I\<close>, [(hyp, [])])] |> snd
      |> rpair st |> Seq.succeed |> Seq.make_results
    end
  fun export_meth _ _ (ctxt, st) =
     TACTIC_CONTEXT ctxt (singleton (Ctxt.get ctxt |> the |> Proof_Context.goal_export ctxt) st |> Seq.single)
  val assume_meth : (Proof.context -> Method.method) context_parser = Args.term >> assume_meth
  val export_meth : (Proof.context -> Method.method) context_parser = Scan.lift (Scan.succeed ()) >> K export_meth
\<close>

method_setup assm = \<open>assume_meth\<close> "Dummy assume method"
method_setup export = \<open>export_meth\<close> "Dummy export method"

lemma "I x" apply (assm x) apply (rule I) done \<comment> \<open>Works in JEdit, but not during build (`isabelle build`)\<close>
lemma "I x" apply (assm x) by (rule I) \<comment> \<open>Same\<close>
lemma "I x" subgoal apply (assm x) by (rule I) done oops \<comment> \<open>Fails\<close>
lemma "I x" subgoal apply (assm x) apply (rule I) apply export done done \<comment> \<open>Works\<close>
lemma "I x" subgoal apply (assm x) apply (rule I) by export done oops \<comment> \<open>Fails\<close>
lemma "I x" proof- show ?thesis apply (assm x) by (rule I) qed \<comment> \<open>Works\<close>
lemma "I x" proof (assm x) show ?thesis by (rule I) qed \<comment> \<open>Works in JEdit, but not during build (`isabelle build`)\<close>
lemma "I x" proof (assm x) show ?thesis by (rule I) qed export \<comment> \<open>Works\<close>
end