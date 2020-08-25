theory Theory_Defs
  imports Pure
begin

setup \<open>
   Sign.declare_const_global
     ((\<^binding>\<open>or\<close>, \<^typ>\<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close>),
     Infixr (Input.string "\<or>", 35, Position.no_range)) #>
   snd
\<close>

setup \<open>
   Sign.declare_const_global
     ((\<^binding>\<open>neg\<close>, \<^typ>\<open>prop \<Rightarrow> prop\<close>),
     Mixfix (Input.string "\<not> _", [40], 40, Position.no_range)) #>
   snd
\<close>

setup \<open>
   pair
    (\<^binding>\<open>or_def\<close>,
     \<^term>\<open>PROP A \<or> PROP B \<equiv> (\<And>P. (PROP A \<Longrightarrow> PROP P) \<Longrightarrow> (PROP B \<Longrightarrow> PROP P) \<Longrightarrow> PROP P)\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_defs false #>
   snd
\<close>

setup \<open>
   pair (\<^binding>\<open>neg_def\<close>, \<^term>\<open>\<not> PROP A \<equiv> (\<And>P. PROP A \<Longrightarrow> PROP P)\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_defs false #>
   snd
\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>excl_mid\<close>, \<^term>\<open>\<And>P. PROP P \<or> \<not> PROP P\<close>) #>>
   apsnd (Thm.forall_elim \<^cterm>\<open>PROP P\<close> #> Drule.generalize ([], ["P"])) #>>
   apfst (K \<^binding>\<open>excl_mid\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_thms #>
   snd
\<close>

ML \<open>
  val prove_double_negation =
    Raw_Simplifier.rewrite_rule \<^context> [@{thm "or_def"}, @{thm "neg_def"}] @{thm "excl_mid"} |>
    Thm.forall_elim \<^cterm>\<open>PROP A\<close> |>
    Thm.instantiate' [] [SOME \<^cterm>\<open>PROP A\<close>] |>
    rpair (Thm.trivial \<^cterm>\<open>PROP A\<close>) |->
    Thm.implies_elim |>
    rpair (Thm.assume \<^cterm>\<open>\<not> \<not> PROP A\<close>) ||>
    Raw_Simplifier.rewrite_rule \<^context> [@{thm "neg_def"}] ||>
    Thm.forall_elim \<^cterm>\<open>PROP A\<close> |->
    Thm.implies_elim |>
    Thm.implies_intr \<^cterm>\<open>\<not> \<not> PROP A\<close> |>
    Drule.generalize ([], ["A"]) |>
    pair \<^binding>\<open>double_negation\<close> |>
    Thm.no_attributes |>
    Global_Theory.add_thm #>
    snd
\<close>

setup \<open>prove_double_negation\<close>

thm double_negation

setup \<open>Sign.add_types_global [(\<^binding>\<open>set\<close>, 1, NoSyn)]\<close>

setup \<open>
   Sign.declare_const_global
     ((\<^binding>\<open>elem\<close>, \<^typ>\<open>'a \<Rightarrow> 'a set \<Rightarrow> prop\<close>),
     Infix (Input.string "\<in>", 50, Position.no_range)) #>
   snd
\<close>

setup \<open>
   Sign.declare_const_global
     ((\<^binding>\<open>Collect\<close>, \<^typ>\<open>('a \<Rightarrow> prop) \<Rightarrow> 'a set\<close>), Mixfix.mixfix "({_})") #>
   snd
\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>elem\<close>, \<^term>\<open>\<And>S x. x \<in> {S} \<equiv> S x\<close>) #>>
   apsnd
     (Thm.forall_elim \<^cterm>\<open>S :: _ \<Rightarrow> prop\<close> #>
      Thm.forall_elim \<^cterm>\<open>x\<close> #>
      Drule.generalize (["'a"], ["S", "x"])) #>>
   apfst (K \<^binding>\<open>elem\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_thms #>
   snd
\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>set\<close>, \<^term>\<open>\<And>S x. {\<lambda> x. x \<in> S} \<equiv> S\<close>) #>>
   apsnd
     (Thm.forall_elim \<^cterm>\<open>S :: _ set\<close> #>
      Thm.forall_elim \<^cterm>\<open>x :: 'b\<close> #>
      Drule.generalize (["'a"], ["S", "x"])) #>>
   apfst (K \<^binding>\<open>set\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_thms #>
   snd
\<close>

ML \<open>
  val prove_set_eq_iff =
    Thm.assume \<^cterm>\<open>x \<in> A\<close> |>
    Raw_Simplifier.rewrite_rule \<^context> [Thm.assume \<^cterm>\<open>A :: 'a set \<equiv> B\<close>] |>
    Thm.implies_intr \<^cterm>\<open>x \<in> A\<close> |>
    rpair (Thm.assume \<^cterm>\<open>x \<in> B\<close>) ||>
    Raw_Simplifier.rewrite_rule \<^context> [Thm.assume \<^cterm>\<open>A :: 'a set \<equiv> B\<close> |> Thm.symmetric] ||>
    Thm.implies_intr \<^cterm>\<open>x \<in> B\<close> |->
    Thm.equal_intr |>
    Thm.forall_intr \<^cterm>\<open>x\<close> |>
    Thm.implies_intr \<^cterm>\<open>A :: 'a set \<equiv> B\<close> |>
    rpair @{thm set} ||>
    Thm.instantiate' [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>A :: 'a set\<close>] ||>
    Thm.symmetric ||>
    pair (Thm.assume \<^cterm>\<open>\<And> x. x \<in> A \<equiv> x \<in> B\<close>) ||>
    apfst (Thm.forall_elim \<^cterm>\<open>x\<close> #> Drule.generalize ([], ["x"]) #> single) ||>
    uncurry (Raw_Simplifier.rewrite_rule \<^context>) ||>
    pair @{thm "set"} ||>
    apfst (Thm.instantiate' [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>B :: 'a set\<close>] #> single) ||>
    uncurry (Raw_Simplifier.rewrite_rule \<^context>) ||>
    Thm.implies_intr \<^cterm>\<open>\<And> x. x \<in> A \<equiv> x \<in> B\<close> |->
    Thm.equal_intr |>
    Drule.generalize (["'a"], ["A", "B"]) |>
    pair \<^binding>\<open>set_eq_iff\<close> |>
    Thm.no_attributes |>
    Global_Theory.add_thm #>
    snd
\<close>

setup \<open>prove_set_eq_iff\<close>

thm set_eq_iff

end