theory Forward_Resolution
  imports Main
begin

definition "w s t \<equiv> SOME x. x \<in> s - t \<or> x \<in> t - s"

text \<open>
Theorems:
  \<bullet> @{thm eq_reflection}
  \<bullet> @{thm someI_ex}
  \<bullet> @{thm HOL.nnf_simps(5)}
  \<bullet> @{thm conj_commute}
  \<bullet> @{thm Diff_iff}
  \<bullet> @{thm set_eq_iff}
  \<bullet> @{thm not_all}
  \<bullet> @{thm w_def}
  \<bullet> @{thm singleton_iff}
  \<bullet> @{thm UnE}
  \<bullet> @{thm atomize_not}
  \<bullet> @{thm not_less}

Interfaces:
  \<bullet> Thm.reflexive
  \<bullet> Thm.symmetric
  \<bullet> Thm.abstract_rule
  \<bullet> Thm.assume
  \<bullet> Thm.combination
  \<bullet> Thm.implies_intr
  \<bullet> Thm.implies_elim
  \<bullet> Thm.eq_thm_prop
  \<bullet> Drule.generalize
  \<bullet> Drule.zero_var_indexes
  \<bullet> Global_Theory.store_thm
  \<bullet> Object_Logic.rulify
  \<bullet> Drule.equal_elim_rule1
  \<bullet> Drule.multi_resolve
  \<bullet> OF
  \<bullet> RS
  \<bullet> Drule.instantiate'_normalize
  \<bullet> Lin_Arith.simproc

Steps:
  \<^enum> Prove statement \<open>x \<equiv> y \<Longrightarrow> P x \<equiv> P y\<close>
  \<^enum> Write an auxiliary function to turn HOL (object) equalities to meta-equalities
  \<^enum> Write an auxiliary functions to substitute n-th occurrence and all accurrences of an equalitiy's LHS in a theorem
  \<^enum> Using the theorems given above and the definition @{thm w_def}, prove the statement:
    \<open>s \<noteq> t \<Longrightarrow> w s t \<in> s - t \<or> w s t \<in> t - s\<close>
  \<^enum> Using auxiliary simproc \<open>Lin_Arith.simproc\<close>, prove the following statement:
    \<open>x \<in> {1} \<union> {2} \<Longrightarrow> x \<le> 2\<close>
\<close>

\<comment> \<open>declare [[unify_trace_failure]]\<close>

\<comment> \<open>
\<^theory_text>\<open>
lemma set_neqD:
  "s \<noteq> t \<Longrightarrow> w s t \<in> s \<and> w s t \<notin> t \<or> w s t \<notin> s \<and> w s t \<in> t"
proof-
  assume "s \<noteq> t"
  then obtain x where "(x \<in> s) \<noteq> (x \<in> t)" unfolding set_eq_iff not_all by (elim exE)
  hence "x \<in> s \<and> x \<notin> t \<or> x \<notin> s \<and> x \<in> t" unfolding HOL.nnf_simps(5) .
  hence "x \<in> s \<and> x \<notin> t \<or> x \<in> t \<and> x \<notin> s" by (subst (asm) (2) conj_commute)
  thus ?thesis unfolding w_def Diff_iff
    by (subst (8) conj_commute) (erule someI[where P="\<lambda> x.  x \<in> s \<and> x \<notin> t \<or> x \<in> t \<and> x \<notin> s"])
qed
\<close>
\<close>

lemmas sets = emptyE case_split UnE IntE DiffE singletonE

ML \<open>
local
  val cong = \<comment> \<open>Proving \<open>x \<equiv> y \<Longrightarrow> P x \<equiv> P y\<close>\<close>
    let
      val asm = \<^cprop>\<open>x :: 'a \<equiv> y\<close>
    in
      \<^cterm>\<open>P :: 'a \<Rightarrow> prop\<close> |>
      Thm.reflexive |>
      rpair (Thm.assume asm) |->
      Thm.combination |>
      Thm.implies_intr asm |>
      Drule.generalize (["'a"], ["P", "x", "y"])
    end
  val meta_eq = try (fn r => r RS @{thm eq_reflection}) |> perhaps \<comment> \<open>Ensure meta equality (\<open>\<equiv>\<close> vs. \<open>=\<close>)\<close>
  fun subst' ctxt cE n thm = \<comment> \<open>Substitute nth occurrence of cE in thm\<close>
    let
      fun diff thm' = Thm.eq_thm_prop (thm, thm') |> not
    in
      Object_Logic.rulify ctxt cE |>
      meta_eq |>
      single |>
      curry op OF cong |>
      single |>
      curry op OF Drule.equal_elim_rule1 |>
      (fn thm' => Drule.multi_resolve (SOME ctxt) [thm] thm') |>
      Seq.filter diff |>
      Seq.chop n |>
      fst |>
      try List.last
   end
  fun subst ctxt cE n = subst' ctxt cE n #> the
  fun subst_all ctxt cE = perhaps_loop (subst' ctxt cE 1) #> the
in
  val prove_set_neqD =
    let
      val asm = \<^cprop>\<open>(s :: 'a set) \<noteq> t\<close>
      val someI_ex =
         @{thm someI_ex} |>
         Drule.instantiate'_normalize [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>\<lambda> x. x \<in> s \<and> x \<notin> t \<or> x \<in> t \<and> x \<notin> s\<close>]
      val nnf_simp =
         @{thm HOL.nnf_simps(5)} |>
         Drule.instantiate'_normalize [] [SOME \<^cterm>\<open>P x :: bool\<close>, SOME \<^cterm>\<open>Q x :: bool\<close>] |>
         Drule.generalize ([], ["P", "Q"]) |>
         meta_eq |>
         Thm.abstract_rule "x" \<^cterm>\<open>x\<close>
      val conj_commute =
         @{thm conj_commute} |>
         Drule.instantiate'_normalize [] [SOME \<^cterm>\<open>x \<notin> s\<close>, SOME \<^cterm>\<open>x \<in> t\<close>] |>
         meta_eq |>
         Thm.abstract_rule "x" \<^cterm>\<open>x\<close>
     val diff =
         @{thm Diff_iff} |>
         Drule.instantiate'_normalize [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>x :: 'a\<close>] |>
         meta_eq |>
         Thm.symmetric |>
         Thm.abstract_rule "x" \<^cterm>\<open>x\<close>
    in
      Thm.assume asm |>
      subst \<^context> @{thm set_eq_iff} 1 |>
      subst \<^context> @{thm not_all} 1 |>
      subst \<^context> nnf_simp 1 |>
      subst \<^context> conj_commute  1 |>
      Thm.implies_elim someI_ex |>
      subst_all \<^context> diff |>
      subst_all \<^context> (@{thm w_def} |> Thm.symmetric) |>
      Thm.implies_intr asm |>
      Drule.generalize (["'a"], ["s", "t"]) |>
      Drule.zero_var_indexes |>
      pair \<^binding>\<open>set_neqD\<close> |>
      Global_Theory.store_thm #>
      snd
    end
  val prove_sample1 =
    let
      val in_Un = \<^cprop>\<open>x \<in> {1} \<union> {2 :: int}\<close>
      val gt2 = \<^cprop>\<open>(2 :: int) < x\<close>
      val in_1 = \<^cprop>\<open>x \<in> {1 :: int}\<close>
      val in_2 = \<^cprop>\<open>x \<in> {2 :: int}\<close>
      val False1 =
        Thm.assume in_1 |>
        subst_all \<^context> @{thm singleton_iff} |>
        rpair (Thm.assume gt2) |->
        subst_all \<^context> |>
        pair (Lin_Arith.simproc \<^context> \<^cterm>\<open>2 < (1 :: int)\<close> |> the) |->
        subst_all \<^context> |>
        Thm.implies_intr in_1
      val False2 =
        Thm.assume in_2 |>
        subst_all \<^context> @{thm singleton_iff} |>
        rpair (Thm.assume gt2) |->
        subst_all \<^context> |>
        pair (Lin_Arith.simproc \<^context> \<^cterm>\<open>2 < (2 :: int)\<close> |> the) |->
        subst_all \<^context> |>
        Thm.implies_intr in_2
      val thm =
        (Thm.assume in_Un RS @{thm UnE}) |>
        curry op COMP False1 |>
        curry op COMP False2 |>
        Thm.implies_intr gt2 |>
        Thm.equal_elim (@{thm atomize_not} |>  Drule.instantiate'_normalize [] [SOME \<^cterm>\<open>(2 :: int) < x\<close>]) |>
        Thm.implies_intr in_Un |>
        subst_all \<^context> @{thm not_less} |>
        Drule.generalize ([], ["x"]) |>
        Drule.zero_var_indexes
    in
      thm |>
      pair \<^binding>\<open>sample1\<close> |>
      Global_Theory.store_thm #>
      snd
    end
end
\<close>

setup \<open>prove_set_neqD\<close>
setup \<open>prove_sample1\<close>

thm set_neqD
thm sample1

end