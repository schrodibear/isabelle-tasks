theory Forward_Reasoning_Example
  imports Main
begin
context
  fixes wf_subst eval M Z F const \<sigma> B y a
  assumes rule1: "\<forall>\<sigma>. wf_subst \<sigma> \<longrightarrow> eval M Z \<sigma> F = B True" and rule2: "wf_subst (\<lambda>v. if v = y then const a else \<sigma> v)"
begin
lemmas rule0 = spec[where P="\<lambda> x. P x \<longrightarrow> Q x" for P Q, THEN mp, where ?'h2="'a \<Rightarrow> 'b"]

thm rule0[OF rule1, OF rule2]
thm rule0[OF rule1 rule2]
declare [[ML_print_depth=100, unify_search_bound=100, unify_trace_types]]
ML \<open>
  val rule0 = @{thm rule0}
  val rule1 = @{thm rule1}
  val rule2 = @{thm rule2}
  val r = Thm.biresolution NONE false [(false, rule2)] 2 rule0 |> Seq.list_of
\<close>
end
end