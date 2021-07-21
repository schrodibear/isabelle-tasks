theory Sample_Forward_Proofs
imports Main
begin
ML \<open>
  Thm.combination (Thm.reflexive \<^cterm>\<open>P :: 'a \<Rightarrow> prop\<close>) (Thm.assume \<^cprop>\<open>x \<equiv> y\<close>)
  |> Thm.implies_intr \<^cprop>\<open>x \<equiv> y\<close> |> Drule.store_standard_thm \<^binding>\<open>substitutivity\<close>
\<close>

lemma sym: "s = t \<Longrightarrow> t = s" using subst[where P="\<lambda>x. x = s", OF _ refl] .
lemma ssubst: "t = s \<Longrightarrow> P s \<Longrightarrow> P t" using subst[OF sym] .
lemma iffD2: "P = Q \<Longrightarrow> Q \<Longrightarrow> P" using ssubst .
lemma TrueI: True using
    True_def[THEN substitutivity,
      THEN equal_elim_rule2[where psi="True" and phi="(\<lambda>x. x) = (\<lambda>x. x)"], OF refl] .
lemma eqTrueE: "P = True \<Longrightarrow> P" using iffD2[OF _ TrueI] .
lemma fun_cong: "f = g \<Longrightarrow> f x = g x" using subst[where P="\<lambda>g. f x = g x" and s=f, OF _ refl] .
lemma spec: "\<forall>x. P x \<Longrightarrow> P x" using
  All_def[THEN substitutivity, THEN equal_elim_rule1[where phi="All P" for P, THEN fun_cong], THEN eqTrueE] .

lemma "x \<in> {1 :: int} \<union> {2} \<Longrightarrow> x = 1 \<or> x = 2" ML_prf \<open>Config.put Blast.trace true |> Context.map_proof |> Context.>>\<close>
  by blast
end