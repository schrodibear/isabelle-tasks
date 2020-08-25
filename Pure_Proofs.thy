theory Pure_Proofs
  imports Pure
begin

  \<comment>\<open>Prove the representation of the double negation rule within meta-logic. Note that Pure
    is higher order intuitionistic propositional logic, so it doesn't assume axiom of choice and
    does not even define the negation symbol. So the axiom of choice should be expressed
    explicitly as a premise and an implication @{text \<open>A \<Longrightarrow> False\<close>} should be used in place of
    negation.\<close>

declare [[ML_print_depth=100]]

ML \<open>
   infix 1 or
   val prove_double_negation =
     let
       val neg = rpair \<^cterm>\<open>PROP P\<close> #> Drule.mk_implies #> Thm.all \<^context> \<^cterm>\<open>PROP P\<close>
       val op or =
          apply2 (rpair \<^cterm>\<open>PROP P\<close> #> Drule.mk_implies) ##>
          rpair \<^cterm>\<open>PROP P\<close> ##>
          Drule.mk_implies #>
          Drule.mk_implies #>
          Thm.all \<^context> \<^cterm>\<open>PROP P\<close>
       val excl_mid = Thm.all \<^context> \<^cterm>\<open>PROP Q\<close> (\<^cterm>\<open>PROP Q\<close> or neg \<^cterm>\<open>PROP Q\<close>)
       val a = \<^cterm>\<open>PROP A\<close>
       val dbl_neg = neg (neg a)

       val a_triv = Thm.trivial a
       val dbl_neg_inst = Thm.assume dbl_neg |> Thm.forall_elim a
       val thm =
         Thm.assume excl_mid |>
         Thm.forall_elim a |>
         Thm.forall_elim a |>
         rpair a_triv |->
         Thm.implies_elim |>
         rpair dbl_neg_inst |->
         Thm.implies_elim |>
         Thm.implies_intr dbl_neg |>
         Thm.implies_intr excl_mid |>
         Drule.generalize ([], ["A"])
     in
       (\<^binding>\<open>double_negation\<close>, thm) |>
       Global_Theory.store_thm #>
       snd
     end

  fun prove_double_negation_eqs thy =
    let
      val or_def = \<^cterm>\<open>or \<equiv> \<lambda> A B. (\<And>P. (PROP A \<Longrightarrow> PROP P) \<Longrightarrow> (PROP B \<Longrightarrow> PROP P) \<Longrightarrow> PROP P)\<close>
      val neg_def = \<^cterm>\<open>neg \<equiv> \<lambda> A. (\<And>P. PROP A \<Longrightarrow> PROP P)\<close>
    in
      Thm.reflexive \<^cterm>\<open>\<lambda> f g. ((\<And> Q. PROP f Q (g Q)) \<Longrightarrow> PROP g (g A) \<Longrightarrow> PROP A)\<close> |>
      rpair (Thm.assume or_def) |->
      Thm.combination |>
      rpair (Thm.assume neg_def) |->
      Thm.combination |>
      Thm.symmetric |>
      Conv.fconv_rule (Thm.beta_conversion true) |>
      Drule.generalize ([], ["A"]) |>
      rpair (Global_Theory.get_thm thy "double_negation") |->
      Thm.equal_elim |>
      Thm.implies_intr or_def |>
      Thm.implies_intr neg_def |>
      Drule.generalize ([], ["or", "neg"]) |>
      pair \<^binding>\<open>double_negation_eqs\<close> |>
      rpair thy |->
      Global_Theory.store_thm |>
      snd
   end
\<close>

setup \<open>prove_double_negation\<close>

setup \<open>prove_double_negation_eqs\<close>

abbreviation (output) neg ("\<not> _") where "\<not> Q \<equiv> (\<And> P. (PROP Q \<Longrightarrow> PROP P))"

abbreviation (output) or ("_ \<or> _") where
  "A \<or> B \<equiv> (\<And> P. \<lbrakk>PROP A \<Longrightarrow> PROP P; PROP B \<Longrightarrow> PROP P\<rbrakk> \<Longrightarrow> PROP P)"

thm double_negation
thm double_negation_eqs
end
