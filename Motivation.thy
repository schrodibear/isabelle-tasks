section \<open>Motivation\<close>

(*<*)
theory Motivation
  imports Main
begin
(*>*)

fun remove_nth :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_nth i [] = []" |
  "remove_nth 0 (x # xs) = xs" |
  "remove_nth (Suc i) (x # xs) = x # remove_nth i xs"

lemma remove_nth_take_drop: "remove_nth i xs = take i xs @ drop (Suc i) xs" proof (induct xs arbitrary: i)
  case Nil then show ?case by simp
next case (Cons a xs) then show ?case by (cases i) auto
qed

subsection \<open>Abbreviations vs. definitions\<close>

lemma remove_nth_prefix: "\<lbrakk>i < n; n < length xs\<rbrakk> \<Longrightarrow> remove_nth n xs ! i = xs ! i"
  unfolding remove_nth_take_drop nth_append by simp
lemma remove_nth_prefix': "n < length xs \<Longrightarrow> \<forall>i < n. remove_nth n xs ! i = xs ! i"
  by (intro allI impI) (rule remove_nth_prefix)

text \<open>
  \<^emph>\<open>Intuitive assumption\<close>:
  \<^thm>"allI" "appropriately" introduces universal quantifiers in the conclusion of the current goal\<dots>
\<close>
text \<open>Let's try it out\<dots>\<close>

lemma remove_nth_postfix: "\<lbrakk>n \<le> i; i < length xs\<rbrakk> \<Longrightarrow> remove_nth n xs ! i = xs ! (i + 1)"
  unfolding remove_nth_take_drop nth_append by (simp add: min.absorb2)
lemma remove_nth_postfix': "\<forall>i\<in>{n..<length xs}. remove_nth n xs ! i = xs ! (i + 1)"
  \<comment> \<open>using [[unify_trace_failure]]\<close> apply (intro allI impI) apply (rule remove_nth_postfix) \<comment> \<open>Really?!\<close> oops

text \<open>In fact\<dots>\<close>

lemma remove_nth_postfix': "\<forall>i\<in>{n..<length xs}. remove_nth n xs ! i = xs ! (i + 1)"
  by (intro ballI impI, unfold atLeastLessThan_iff, elim conjE) (rule remove_nth_postfix)

subsection \<open>Complex notations involving \<^emph>\<open>parse translations\<close>\<close>

lemma sorted_iff: "sorted xs \<longleftrightarrow> (\<forall>(i, j)\<in>{(i, j) | i j. i < j \<and> j < length xs}. xs ! i \<le> xs ! j)"
  unfolding sorted_iff_nth_mono_less by auto

text \<open>
  \<^emph>\<open>Intuitive assumption\<close>:
  \<^term>\<open>{x. P x}\<close> and \<^term>\<open>{f x | x. P x}\<close> are just some nice notations to represent set comprehensions\<dots>
\<close>
text \<open>Let's try them out once more\<dots>\<close>

definition "mono_pair xs \<equiv> \<lambda> (i, j). i < j \<and> j < length xs"

lemma sorted_iff': "sorted xs \<longleftrightarrow> (\<forall>(i, j)\<in>{u. mono_pair xs u}. xs ! i \<le> xs ! j)"
  unfolding mono_pair_def \<comment> \<open>using [[unify_trace_failure]]\<close> apply (rule sorted_iff) \<comment> \<open>Really?!\<close> oops

text \<open>In fact\<dots>\<close>

lemma Collect_prod_iff: "{u. P u} = {(a, b) | a b. P (a, b)}" by auto
proposition "Collect (\<lambda> u. P u) = Collect (\<lambda>uu. \<exists> a b. uu = (a, b) \<and> P (a, b))" using Collect_prod_iff .

lemma sorted_iff': "sorted xs \<longleftrightarrow> (\<forall>(i, j)\<in>{u. mono_pair xs u}. xs ! i \<le> xs ! j)"
  unfolding mono_pair_def by (subst Collect_prod_iff, subst prod.case) (rule sorted_iff)

subsection \<open>Numerals, type constraints, classes & sorts\<close>

lemma "length xs < length xs + 1" using less_add_one .

text \<open>\<^emph>\<open>Intuitive assumption\<close>: \<^thm>"less_add_one" represents the trivial fact \<open>a < a + 1\<close>\<dots>\<close>
text \<open>Let's try it out\<dots>\<close>

lemma "a < a + 1" using less_add_one . \<comment> \<open>Really?!\<close> oops
lemma "1 < 2" apply simp \<comment> \<open>How come?!\<close> oops

text \<open>In fact\<dots>\<close>

lemma "a < a + 1" for a :: "_::linordered_semidom" using less_add_one .
  \<comment> \<open>Smidom — semi-integral domain — nonzero commutative semiring without zero divisors\<close>
lemma "1 < (2::_::linordered_semidom)" by simp

subsection \<open>Higher-order unification\<close>

lemma "m < n \<Longrightarrow> \<Sum> {m..n} = (n - m + 1) * (m + n) div 2" for m n :: nat
  unfolding atomize_imp by (rule nat_induct, force, auto simp: Suc_diff_le less_Suc_eq)

text \<open>
From a mailing list discussion:
  \<open>In A.1.3 you see that "by" actually has two proof method slots,
   corresponding to "proof" ... "qed". That is practically important, e.g.
   for "by induct auto" proofs --- please don't do "by (induct, auto)".\<close>
  (by one of the main Isabelle developers)
\<close>
text \<open>Let's try out the advice:\<close>
lemma "m < n \<Longrightarrow> \<Sum> {m..n} = (n - m + 1) * (m + n) div 2" for m n :: nat
  unfolding atomize_imp by (rule nat_induct) (force, auto simp: Suc_diff_le less_Suc_eq)

text \<open>
  \<^emph>\<open>Intuitive assumption\<close>:
  Don't write \<^theory_text>\<open>by (method, auto)\<close>, write \<^theory_text>\<open>by method auto\<close>; follow suggestions in A.1.3 of the manual\<dots>\<close>
text \<open>Let's try it out\<dots>\<close>

text \<open>From A.1.3: \<^theory_text>\<open>by m\<^sub>1 m\<^sub>2\<close> \<equiv>  \<^theory_text>\<open>proof m\<^sub>1 qed m\<^sub>2\<close>\<close>

lemma "m < n \<Longrightarrow> \<Sum> {m..n} = (n - m + 1) * (m + n) div 2" for m n :: nat
  unfolding atomize_imp proof (rule nat_induct) qed (force, auto simp: Suc_diff_le less_Suc_eq) \<comment> \<open>Why?!\<close> oops

text \<open>In fact\<dots>\<close>

lemma "m < n \<Longrightarrow> (\<Sum>i\<in>{m..n}. i) = (n - m + 1) * (m + n) div 2" for m n :: nat
  unfolding atomize_imp proof (rule nat_induct[where n=n]) qed (auto simp: Suc_diff_le less_Suc_eq)
\<comment> \<open>But better\<close>
lemma "m < n \<Longrightarrow> (\<Sum>i\<in>{m..n}. i) = (n - m + 1) * (m + n) div 2" for m n :: nat
  by (induct n) (auto simp: Suc_diff_le less_Suc_eq)

subsection \<open>Higher-order resolution and refinement rule\<close>

lemma "\<forall>a. \<exists>b<a. P b a" (is "\<forall>a. ?P a") if leq: "\<forall>a\<le>i. \<exists>b<a. P b a" and gt: "\<forall>a>i. \<exists>b<a. P b a" for i::"_::linorder"
proof (intro allI)
  fix a show "?P a" proof (cases "a \<le> i" rule: case_split[case_names Leq Gt])
    case Leq
    from leq[rule_format, OF Leq] obtain b where "b < a" "P b a" by (elim exE conjE)
    thus ?thesis by (intro exI conjI)
  next case Gt with gt[rule_format, of a] show ?thesis unfolding not_le .
  qed
qed

text \<open>
  \<^emph>\<open>Intuitive assumption\<close>:
  \<^theory_text>\<open>obtains\<close> clause introduces auxiliary variables that can be later used to fill the holes
  in goal statements e.g. \<open>?b\<close> inside nested proofs\<dots>\<close>
text \<open>Let's try it out again\<dots>\<close>

lemma "\<forall>a. \<exists>b<a. P b a" if leq: "\<forall>a\<le>i. \<exists>b<a. P b a" and gt: "\<forall>a>i. \<exists>b<a. P b a" for i::"_::linorder"
proof (intro allI)
  fix a show "\<exists>b<a. P b a" proof (cases "a \<le> i" rule: case_split[case_names Leq Gt]; intro exI conjI)
    case Leq
    from leq[rule_format, OF Leq] obtain b where "b < a" "P b a" by (elim exE conjE)
    show "b < a" "P b a" \<comment> \<open>Really?!\<close>
      oops

text \<open>In fact\<dots>\<close>
text \<open>\<^theory_text>\<open>obtain\<close> is just a sugar for elimination rule, let's try using @{method elim} instead\<close>

lemma "\<forall>a. \<exists>b<a. P b a" if leq: "\<forall>a\<le>i. \<exists>b<a. P b a" and gt: "\<forall>a>i. \<exists>b<a. P b a" for i::"_::linorder"
  apply (intro allI)
  subgoal for a
    apply (cases "a \<le> i")
    subgoal apply (drule leq[rule_format]) by (elim exE conjE, intro exI conjI)
    subgoal apply (unfold not_le) apply (drule gt[rule_format]) by (elim exE conjE, intro exI conjI)
    done
  done

lemma "\<forall>a. \<exists>b<a. P b a" if leq: "\<forall>a\<le>i. \<exists>b<a. P b a" and gt: "\<forall>a>i. \<exists>b<a. P b a" for i::"_::linorder"
  apply (intro allI)
  subgoal for a
    apply (cases "a \<le> i")
    subgoal apply (drule leq[rule_format]) apply (intro exI conjI) by (elim exE conjE)
        \<comment> \<open>Not possible since \<open>?b2\<close> does not depend on the bound variable \<open>b\<close>\<close>
oops

subsection \<open>General awareness of capabilities\<close>

lemma "finite X \<Longrightarrow> (\<Sum>x\<in>X. \<Sum>y\<leftarrow>ys. f x y) = (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>X. f x y)"
  by (induct X rule: finite_induct) (simp_all add: sum_list_addf) \<comment> \<open>Note the resulting Isabelle output\<close>

text \<open>\<^emph>\<open>Intuitive assumption\<close>: Some strange inherent limitation of pretty-printing\<dots>\<close>
text \<open>Cannot do anything about it\<dots>\<close>

text \<open>In fact\<dots>\<close>

abbreviation (output) "Sum_list f xs \<equiv> sum_list (map f xs)"
print_translation \<open>[Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>Sum_list\<close> \<^const_syntax>\<open>Sum_list\<close>]\<close>
translations "\<Sum>x\<leftarrow>xs. b" \<leftharpoondown>"CONST Sum_list x b xs"

lemma sum_sum_list_perm: "finite X \<Longrightarrow> (\<Sum>x\<in>X. \<Sum>y\<leftarrow>ys. f x y) = (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>X. f x y)"
  by (induct X rule: finite_induct) (simp_all add: sum_list_addf) \<comment> \<open>Note the resulting Isabelle output\<close>

text \<open>Just for illustration: more of the nice output\<close>
lemma "finite X \<Longrightarrow> (\<Sum>x\<in>X. \<Sum>y\<leftarrow>ys. f x y) = (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>X. f x y)"
proof (induct X rule: finite_induct)
  case empty thus ?case by simp
next
  case (insert x X)
  from insert(1,2) have "(\<Sum>x\<in>insert x X. \<Sum>y\<leftarrow>ys. f x y) = (\<Sum>y\<leftarrow>ys. f x y) + (\<Sum>x\<in>X. \<Sum>y\<leftarrow>ys. f x y)" by simp
  also from insert(3) have "\<dots> = (\<Sum>y\<leftarrow>ys. f x y) + (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>X. f x y)" by simp
  also from insert(1,2) have "\<dots> = (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>insert x X. f x y)" by (simp add: sum_list_addf)
  finally show ?case .
qed

(*<*)
end
(*>*)