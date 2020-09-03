theory Forward_Reasoning
  imports Main
begin

section \<open>Forward (elim-) composition and resolution\<close>

subsection \<open>Isabelle/ML interfaces\<close>

text \<open>
  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.bicompose\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context option\<close>)\\
  (\<open>config\<close> : \<^ML_type>\<open>{flatten : bool, match : bool, incremented : bool}\<close>)\\
  (\<open>rule\<close> : \<^ML_type>\<open>bool * thm * int\<close>)\\
  (\<open>i\<close> : \<^ML_type>\<open>int\<close>)\\
  (\<open>st\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm Seq.seq\<close>
  \end{tabular}\\
  The most basic Isabelle reasoning primitive implementing \<^emph>\<open>forward composition\<close> of a \<^emph>\<open>rule\<close> with a \<^emph>\<open>proof state\<close>.
  Let's define a \<^emph>\<open>proof state\<close> as a theorem of the following form:\\
  \<open>S\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>i \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>n \<Longrightarrow> G\<close>\\
  We'll call the premises \<open>S\<^sub>1, \<dots>, S\<^sub>n\<close> of such a theorem the \<^emph>\<open>subgoals\<close>, and the conclusion the (original)
  \<^emph>\<open>statement\<close>. Meanwhile, let's also define a \<^emph>\<open>rule\<close> in a totally similar way:
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>j \<Longrightarrow> \<dots> A\<^sub>m \<Longrightarrow> C\<close>,\\
  where \<open>A\<^sub>j\<close> is called the \<open>j\<close>-th \<^emph>\<open>assumption\<close> of the rule and \<open>C\<close> is called the \<^emph>\<open>conclusion\<close>. Note that \<^emph>\<open>both\<close>
  the subgoals and the assumptions can themselves be arbitrarily complex propositions (of type \<^typ>\<open>prop\<close>) and
  thus \<^emph>\<open>do not\<close> have to be object-logic terms and can include meta-connectives such as \<open>\<Longrightarrow>\<close> and \<open>\<And>\<close>. Thus the
  interpretation of both the proof state and the rule is generally \<^emph>\<open>ambiguous\<close>, since the statement \<open>G\<close> as well as
  the conclusion \<open>C\<close> can include implications, which makes the number of subgoals and premises not fully determined
  solely by the shape of the corresponding theorem. Yet we can still count both the subgoals and the assumptions
  from the left, so any particular positive number is unambiguous (the counting here stats from \<open>1\<close>).

  Now let's consider a rule \<open>r\<close> with (at least) \<open>m\<close> premises. Let's then regard the remaining consequent of the rule
  its conclusion \<open>C\<close> (even if it includes implications). Let's also consider the subgoal \<open>S\<^sub>i\<close> with index \<open>i\<close>.
  Both \<open>C\<close> and \<open>S\<^sub>i\<close> can be considered terms depending on the \<^emph>\<open>schematic variables\<close> (both \<^emph>\<open>term\<close> and \<^emph>\<open>type\<close> variables)
  that occur in them. Let's consider the rule's and the state's variable scopes \<^emph>\<open>together\<close> as if the variables are
  \<^emph>\<open>shared\<close> between them. Now we can intoroduce the notion of a \<^emph>\<open>unifier\<close> \<open>\<theta>\<close>, which is a substitution that makes two
  terms syntactically equal to each other: \<open>\<theta>C \<equiv> \<theta>S\<^sub>i\<close>. Note that in Isabelle we consider \<^emph>\<open>higher-order\<close> unification,
  where terms may contain lambda-abstractions and applications of schematic variables to arbitrary arguments. The
  problem of deciding whether there exists a unifier for two arbitrary such terms is \<^emph>\<open>undecidable\<close> in general, and
  moreover, even if some unifier does exist it may not me unique even up to instantiation. Therefor there's no notion
  of the most general unifier. Instead what we get is a possibly infinite sequence of unifiers. Let's designate
  an arbitrary member of such a sequence as \<open>\<theta>\<^sub>k\<close> and the whole sequence as \<open>\<dots> \<langle>\<theta>\<^sub>k\<rangle> \<dots>\<close>. Now in the default mode, the
  result of the function \<^ML>\<open>Thm.bicompose\<close> applied to a \<open>rule\<close> \<^ML_text>\<open>(false, r, m)\<close> (where \<open>r\<close> has the form
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>j \<Longrightarrow> \<dots> A\<^sub>m \<Longrightarrow> C\<close>), a subgoal index \<open>i\<close> and a state \<open>st\<close> (\<open>S\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>i \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>n \<Longrightarrow> G\<close>) is
  the following possibly infinite sequence of theorems:\\
  \<open>\<dots> \<langle>\<theta>\<^sub>kS\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> \<theta>\<^sub>kS\<^bsub>i-1\<^esub> \<Longrightarrow> \<theta>\<^sub>kA\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> \<theta>\<^sub>kA\<^bsub>m-1\<^esub> \<Longrightarrow> \<theta>\<^sub>kS\<^bsub>i+1\<^esub> \<Longrightarrow> \<dots> \<Longrightarrow> \<theta>\<^sub>kS\<^sub>n \<Longrightarrow> \<theta>\<^sub>kG\<rangle> \<dots>\<close>,\\
  given the side-condition that for every substitution \<open>\<theta>\<^sub>k\<close>, \<open>\<theta>\<^sub>kC \<equiv> \<theta>\<^sub>kS\<^sub>i\<close>. As can be seen from that explanation, the
  conclusion \<open>C\<close> of the rule \<open>r\<close> should unify with the \<open>i\<close>-th subgoal \<open>S\<^sub>i\<close> of the state producing a substitution
  of the shared variables that is applied both to the rule and the state before replacing the subgoal \<open>S\<^sub>i\<close> with
  the sequence of assumptions \<open>A\<^sub>1, \<dots> A\<^sub>m\<close>, \<open>m \<ge> 0\<close>. This is the most general form of the operation that is called
  \<^emph>\<open>composition\<close> of the rule \<open>r\<close> with the state \<open>st\<close> in Isabelle parlance. If not specified otherwise, the default
  values of additional parameters in this operation are assumed to be \<open>m = 0\<close> and \<open>i = 1\<close>.

  Now let's introduce an Isabelle-specific version of such general operation. It's called \<^emph>\<open>elim-composition\<close> and
  is only different from the general composition in that it imposes an additional constraint on the unifiers \<open>\<theta>\<^sub>k\<close>,
  namely: There should exist an assumption \<open>A\<^sub>j\<close>, \<open>1 \<le> j \<le> m\<close> such that it itself has the form
  \<open>B\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> B\<^sub>l \<Longrightarrow> B\<close>, where \<open>\<theta>\<^sub>kB\<^sub>p \<equiv> B\<close> for some \<open>1 \<le> p \<le> l\<close>. Intuitively it means that the assumption
  is in a certain way trivially equivalent to identical truth modulo instantiation of schematic variables. This is
  called \<^emph>\<open>proving by assumption\<close> in Isabelle parlance,
  since the assumption momentarily becomes a new subgoal in the resulting proof state and that emerging subgoal is
  then immediately solved by assumption. At the first glance this support of a rather special case of composition
  may seem rather artificial, but in fact it is provided with the appropriate optimized implementation
  \<^emph>\<open>directly in the proof kernel\<close> itself due to being a very common case in proofs, including the ones produced by
  rather powerful proof methods such as @{method auto}. Actually, the whole composition (and resolution, see below)
  machinery of Isabelle is implemented directly in the kernel due to efficiency considerations, since all the
  manipulations needed to perform the actual composition can themselves be certified within the proof kernel. However,
  the number of inner intermediate kernel interface calls would be quite significant and that would create a very
  unpleasant proof overhead for such a basic proof operation as composition. The elim-composition is enabled by
  changing the \<^emph>\<open>elim\<close> \<^emph>\<open>flag\<close> in the \<open>rule\<close> parameter to \<^ML>\<open>true\<close> i.\,e. \<^ML_text>\<open>(true, r, m)\<close>. This variant
  of composition is mostly relevant for \<^emph>\<open>elimination rules\<close> of the form\\
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^bsub>m-r\<^esub> \<Longrightarrow> (B\<^sub>1\<^sub>,\<^sub>1\<^esub> \<Longrightarrow> \<dots> \<Longrightarrow> B\<^sub>1\<^sub>,\<^bsub>l\<^sub>1\<^esub> \<Longrightarrow> C) \<Longrightarrow> \<dots> (B\<^sub>r\<^sub>,\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> B\<^sub>r\<^sub>,\<^bsub>l\<^sub>r\<^esub> \<Longrightarrow> ?C) \<Longrightarrow> ?C\<close>,\\
  where the whole conclusion is just a single schematic variable \<open>?C\<close> (note that there are still \<open>m\<close> assumptions).
  Obviously, in this case the usual constraint
  \<open>\<theta>\<^sub>k?C \<equiv> \<theta>\<^sub>kS\<^sub>i\<close> often becomes too weak, hence the need for the additional constraint. Note also that there are also
  cases, where even though the conclusion is still a single variable \<open>?C\<close>, no additional constraints are needed. This,
  for instance, is the case for the usual case-splitting rule @{thm case_split}. But in these cases an additional
  manual instantiation of the rule is often necessary (as in the corresponding application of the @{method cases}
  method).

  Now let's consider the other additional configuration options that finely control the composition. The flag
  \<open>flatten\<close> is only relevant for elimination rules and simultaneously enables two things:
  \<^item> Normalization of (meta-) quantifiers in the emerging subgoals \<open>A\<^sub>j\<close> of the form \<open>\<theta>B\<^sub>i\<^sub>,\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> \<theta>B\<^sub>i\<^sub>,\<^bsub>l\<^sub>i\<^esub> \<Longrightarrow> \<theta>C\<close> into
    the prenex normal form;
  \<^item> Deletion of the \<open>j\<close>-th premise, where \<open>A\<^sub>j\<close> was solved by assumption, from every emerging subgoal \<open>A\<^sub>j\<close>.

  Both of these features are mostly relevant for tactical reasoning that builds upon composition and resolution and
  are also integrated directly into the proof kernel for efficiency. The flag \<open>match\<close> ensures that \<^emph>\<open>all\<close> subgoals
  of the proof state \<open>st\<close>, \<^emph>\<open>including\<close> the subgoal \<open>S\<^sub>i\<close>, remain unchanged by every substitution \<open>\<theta>\<^sub>k\<close>. This
  is treated as an additional constraint on the resulting sequence of unifiers \<open>\<dots>\<langle>\<theta>\<^sub>k\<rangle>\<dots>\<close>. The semantics of
  the flag \<open>incremented\<close> may seem rather strange, but worth mentioning to avoid some common confusion. The point is
  that schematic term variables in Isabelle are actually treated as \<^emph>\<open>Church-style\<close>, i.\,e. term variables of different
  types are considered different even if they have the same name. For that reason, technically, there is a potential
  for variability in the behavior of composition for term variables that \<^emph>\<open>do not\<close> occur in either \<open>C\<close> or \<open>S\<^sub>i\<close> (as
  well as \<open>B\<^sub>p\<close> or \<open>B\<close> when the elim-flag is enabled). Since the unifier does not contain any explicit
  substitutions of those variables, their \<^emph>\<open>types\<close> can either be matched by their names and unified
  (\<open>incremented = false\<close>) or left as-is, possibly different from each other and potentially incompatible
  (\<open>incremented = true\<close>). Note, again, that the additional type substitutions here are potentially being imposed
  solely by the coinciding names of the variables rather than being implied by the required
  syntactic equalities of the terms. The only remaining optional parameter is the proof context \<open>ctxt\<close>. Indeed, it
  is optional and only controls the amount of debugging information that can be printed during unification. Dy default
  no debug output is enabled. However, sometimes the well-known configuration option @{attribute unify_trace_failure}
  may be helpful when unification fails for large complicated terms.

  \<^bigskip>
\<close>

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

lemma goal: "(\<And> x. A x \<Longrightarrow> B x \<Longrightarrow> C) \<Longrightarrow> (U \<Longrightarrow> V \<Longrightarrow> D x  y) \<Longrightarrow>  G r" sorry
lemma prem1: "C" sorry
lemma prem2: "(True \<Longrightarrow> Y ) \<Longrightarrow>(\<And> x. Y \<Longrightarrow> T) \<Longrightarrow>U \<Longrightarrow> V \<Longrightarrow> D x y" sorry
lemma prem3: "D \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> C" sorry
lemma prem4: "D \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> C" sorry
lemma prem5: "V y \<Longrightarrow> C" sorry
lemma prem6: "\<And> x y. (\<And> g. \<And> y. R g \<Longrightarrow> (\<And> q. Q q \<Longrightarrow> S x q g)) \<Longrightarrow> U \<Longrightarrow> V \<Longrightarrow> D x y" sorry
lemma prem33: "\<And> x. A x \<Longrightarrow> B x \<Longrightarrow> C" sorry
lemma prem7: "(False \<Longrightarrow>  True \<Longrightarrow> [()] = [()] \<Longrightarrow>  [()] = [()]) \<Longrightarrow> ([()] = [()] \<Longrightarrow> (\<And> u. PROP UU)) \<Longrightarrow> PROP UU" sorry

ML \<open>(@{thm prem33} |> Thm.forall_intr \<^cterm>\<open>x\<close>) COMP @{thm goal}\<close>

ML \<open>
  Thm.bicompose
    (SOME \<^context>)
    {flatten = true, incremented = false, match = false}
    (true, @{thm prem2}, 2)
    2
    @{thm goal} |>
  Seq.hd\<close>

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