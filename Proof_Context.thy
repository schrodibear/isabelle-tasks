theory Proof_Context
  imports Main
  keywords "guess_by_rule" :: prf_asm % "proof" and "rule_context" :: thy_defn
begin

ML \<open>
infix 0 CCOMPN CCOMP
signature BASIC_UTIL = sig
  val CCOMPN : thm * (int * thm) -> thm
  val CCOMP : thm * thm -> thm
end
structure Util = struct
  fun super_thy (thy1, thy2) =
    if Context.subthy (thy1, thy2) then thy1
    else if Context.subthy (thy2, thy1) then thy2
    else raise THEORY ("No proper supertheory", [thy1, thy2])
  val super_thy_of = apply2 Thm.theory_of_thm #> super_thy
  fun unifiers context max (t1, t2) =
    Unify.unifiers (context, Envir.empty max, [(t1, t2)])
    |> Seq.map
      (fn (e as Envir.Envir { tyenv, tenv, ... }, _) =>
        (tyenv |> Vartab.dest |>
         map
           (fn (xi, (S, T)) =>
             ((xi, S), T |> Envir.norm_type tyenv |> Context.cases Thm.global_ctyp_of Thm.ctyp_of context)),
         tenv |> Vartab.dest |>
         map
           (fn (xi, (T, t)) =>
             ((xi, Envir.norm_type tyenv T),
              Envir.norm_term e t |> Context.cases Thm.global_cterm_of Thm.cterm_of context))))
  fun r CCOMPN (i, s) =
    let
      val thy = super_thy_of (r, s)
      val max = Thm.maxidx_of r + Thm.maxidx_of s + 2
    in
      Logic.get_goal (Thm.prop_of s) i
      |> pair [] |> perhaps (I ##>> Logic.dest_all #>> swap #>> uncurry cons |> try |> perhaps_loop)
      |>> Term.rename_wrt_term (Thm.prop_of r)
      ||> pair (Thm.forall_elim_vars (Thm.maxidx_of r + 1) r |> Drule.incr_indexes s)
      ||> `(apfst Thm.prop_of #> unifiers (Context.Theory thy) max #> Seq.hd) ||> apsnd fst
      ||> `(uncurry instantiate_normalize) ||> apsnd (fst o fst)
      |> (fn (vars, (r, tys)) =>
        vars
        |> map (typ_subst_TVars (map (fst |> apfst ##> Thm.typ_of) tys) |> apsnd #> Free #> Thm.global_cterm_of thy)
        |> rpair r |-> forall_intr_list
        |> rpair (i, s) |> Scan.triple2 |> Drule.compose |> zero_var_indexes)
    end
  fun r CCOMP s = r CCOMPN (1, s)
  val id_t = Unsynchronized.ref NONE
  fun register_id_ (t : term) = (id_t := SOME t; t)
  fun id_ T = !id_t |> the |> dest_Const ||> K (T --> T) |> Const
end
structure Basic_Util : BASIC_UTIL = Util
open Basic_Util
\<close>

setup \<open>Sign.declare_const_global ((\<^binding>\<open>id_\<close>, \<^typ>\<open>'a \<Rightarrow> 'a\<close>), NoSyn) #>> Util.register_id_ #> snd\<close>

setup \<open>
  pair (\<^binding>\<open>id__def\<close>, \<^term>\<open>I x \<equiv> x\<close> |> subst_free [(\<^term>\<open>I :: 'a \<Rightarrow> 'a\<close>, Util.id_ \<^typ>\<open>'a\<close>)])
  #>> Thm.simple_fact #-> Global_Theory.add_defs false #> snd
\<close>

ML \<open>
structure Hilbert_Guess = struct
  fun meta_eq e = e RS @{thm atomize_eq[THEN equal_elim_rule2]}
  val prod_conv_thms = [@{thm fst_conv}, @{thm snd_conv}] |> map meta_eq
  fun prod_sel_tac ctxt = rewrite_goal_tac ctxt prod_conv_thms THEN' resolve_tac ctxt [@{thm refl}]
  fun wrap_id_ t = Util.id_ (type_of t) $ t
  fun nth_conv ctxt n k =
    let
      val (xs, Ts) =
        ("a", Name.aT) |> apply2 (fn s => Name.invent (Variable.names_of ctxt) s n)
        ||> map (rpair (Proof_Context.theory_of ctxt |> Sign.defaultS) #> TFree)
      val ts = xs ~~ Ts |> map Free
      val t = nth ts (k - 1)
      val (last, m) = if n = k then (HOLogic.mk_snd, n - 2) else (HOLogic.mk_fst, k - 1)
      val lhs = HOLogic.mk_tuple ts |> wrap_id_ |> funpow m HOLogic.mk_snd |> last
    in
      Goal.prove ctxt xs [] (HOLogic.mk_eq (lhs, t) |> HOLogic.mk_Trueprop)
        (HEADGOAL (rewrite_goal_tac ctxt [@{thm id__def}] THEN' prod_sel_tac ctxt) |> K)
    end
  val nth_conv = fn ctxt => fn n => if n = 1 then K (@{thm id__def} RS @{thm meta_eq_to_obj_eq}) else nth_conv ctxt n
  val True_simp = @{lemma "(True \<and> A) = A" by simp} |> meta_eq
  fun conj_elim_tac ctxt = (REPEAT_ALL_NEW (eresolve_tac ctxt [@{thm conjE}]) ORELSE' (K all_tac)) THEN' assume_tac ctxt
  fun maybe_skolem ctxt = Variable.is_body ctxt ? Name.skolem
  fun maybe_dest_skolem ctxt = Variable.is_body ctxt ? Name.dest_skolem
  \<comment> \<open>
  Export local theorem \<open>G \<^bold>x\<close> (\<open>thm\<close> over \<open>vars\<close>) valid under \<open>\<^bold>H \<^bold>x\<close> (\<open>chyps\<close>)
  into the global context. Note that \<open>\<^bold>x\<close> \<^emph>\<open>may\<close> occur in \<open>G\<close>, hence the need in all those Hilbert Epsilon tricks.
  What we want to get is basically \<open>\<^bold>H ?\<^bold>x \<Longrightarrow> G' (\<epsilon>(\<^bold>x) (\<And>\<^bold>H) \<^bold>x))\<close>, where bold font denotes vectors, bold in
  parenthesis denotes tuples and \<open>\<epsilon>\<close> is the Hilbert Epsilon-operator.
  Here's the basic approach:
  — (1). \<open>\<^bold>H \<^bold>x \<turnstile> G \<^bold>x \<Longrightarrow> (\<^bold>H \<^bold>x \<Longrightarrow> G \<^bold>x)\<close>
  — (2). \<open>\<dots> \<Longrightarrow> ((\<And>\<^bold>H) \<^bold>x \<Longrightarrow> G \<^bold>x)\<close>
  — (3). \<open>\<dots> \<Longrightarrow> ((\<And>\<^bold>H') (\<^bold>x) \<Longrightarrow> G' (\<^bold>x))\<close>
  — (4). \<open>\<dots> \<Longrightarrow> ((\<And>\<^bold>H') ?x \<Longrightarrow> G' ?x)\<close>
  — (5). \<open>\<dots> \<Longrightarrow> ((\<And>\<^bold>H') ?x \<Longrightarrow> G' (\<epsilon>x (\<And>\<^bold>H') x))\<close>
  — (6). \<open>\<dots> \<Longrightarrow> ((\<And>\<^bold>H') (\<^bold>x) \<Longrightarrow> G' (\<epsilon>x (\<And>\<^bold>H') x))\<close>
  — (7). \<open>\<dots> \<Longrightarrow> (\<^bold>H \<^bold>x \<Longrightarrow> G' (\<epsilon>x (\<And>\<^bold>H') x))\<close>
  — (8). \<open>\<dots> \<Longrightarrow> (\<^bold>H ?\<^bold>x \<Longrightarrow> G' (\<epsilon>(\<^bold>x) (\<And>\<^bold>H) \<^bold>x))\<close>
  \<close>
  fun export0 ctxt vars chyps thm =
    let
      val gens = ([], map fst vars)
      val (gthm, intro) = \<comment> \<open>(1, 2)\<close>
        let
          val phyps = map Thm.term_of chyps
          val ahyps = map (Object_Logic.atomize_term ctxt) phyps
          val pconj =
            ahyps
            |> List.foldl (HOLogic.mk_conj o swap) \<^term>\<open>True\<close>
            |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) [True_simp] []
            |> HOLogic.mk_Trueprop
          val cconj = Thm.cterm_of ctxt pconj
          val intros =
            map
              (HOLogic.mk_Trueprop
               #> curry Logic.mk_implies pconj
               #> Thm.cterm_of ctxt
               #> rpair (HEADGOAL (conj_elim_tac ctxt) |> K) #-> Goal.prove_internal ctxt []
               #> Conv.fconv_rule (Object_Logic.atomize ctxt))
              ahyps |>
            rpair (map (curry Logic.mk_implies pconj #> Thm.cterm_of ctxt) phyps) |>
            op ~~ |>
            map
              (fn (a, g) =>
                Goal.prove_internal ctxt [] g
                  (HEADGOAL (Object_Logic.full_atomize_tac ctxt THEN' resolve_tac ctxt [a]) |> K)
                |> curry op RS (Thm.assume cconj))
          val intro =
            Goal.prove_internal ctxt [] (List.foldr Logic.mk_implies pconj phyps |> Thm.cterm_of ctxt)
              (HEADGOAL
                (Object_Logic.atomize_prems_tac ctxt
                 THEN' rewrite_goal_tac ctxt [@{thm conj_assoc}]
                 THEN' REPEAT_ALL_NEW (ares_tac ctxt [@{thm conjI}, @{thm TrueI}])) |> K)
        in
          fold_rev Thm.implies_intr chyps thm \<comment> \<open>(1)\<close>
          |> fold (curry op CCOMP) intros |> Thm.implies_intr cconj \<comment> \<open>(2)\<close>
          |> rpair intro
        end
      val frees = map Free vars
      val cfrees = map (Thm.cterm_of ctxt) frees
      val n = length vars
      val subs = 1 upto n |> map (nth_conv ctxt n #> meta_eq #> infer_instantiate' ctxt (map SOME cfrees))
      \<comment> \<open>prop of (3):\<close>
      val gprop = gthm |> Thm.prop_of |> subst_free (map (swap o Logic.dest_equals o Thm.prop_of) subs)
      fun induct k = \<comment> \<open>induction rules for (4)\<close>
        let
          val m = n - k - 1
          val sub = HOLogic.mk_tuple (drop m frees)
          val x = Term.variant_frees gprop [("x", type_of sub)] |> the_single
          val subs = apply2 (fn x => take m frees @ [x] |> HOLogic.mk_tuple |> wrap_id_) (sub, Free x) |> single
        in
          gprop
          |> Object_Logic.atomize_term ctxt
          |> Pattern.rewrite_term (Proof_Context.theory_of ctxt) subs []
          |> lambda (Free x) |> Thm.cterm_of ctxt |> SOME |> single
          |> rpair @{thm prod.induct} |-> infer_instantiate' ctxt |> Drule.generalize gens
        end
      val gthm = \<comment> \<open>(3,4,5)\<close>
        Goal.prove_internal ctxt [] (Thm.cterm_of ctxt gprop)
          (HEADGOAL (rewrite_goal_tac ctxt subs THEN' solve_tac ctxt [gthm]) |> K) \<comment> \<open>(3)\<close>
        |> Conv.fconv_rule (Object_Logic.atomize ctxt)
        |> fold_rev Thm.forall_intr cfrees
        |> fold (fn n => fn thm => thm CCOMP induct n) (1 upto n - 1) \<comment> \<open>(4)\<close>
        |> rpair @{thm mp} |> op CCOMP |> rpair (2, @{thm someI2}) |> op CCOMPN \<comment> \<open>(5)\<close>
     val u = \<comment> \<open>instantiation for (6)\<close>
        (gprop, Thm.prop_of gthm) |> apply2 (Logic.dest_implies #> fst)
        |> Util.unifiers (Context.Proof ctxt) (Thm.maxidx_of gthm) |> Seq.hd
     val eps_simps = \<comment> \<open>optional rewrite rule for (8)\<close>
       let
         val vars' = map (maybe_dest_skolem ctxt |> apfst) vars
         val frees' = vars' |> Term.variant_frees (gprop |> subst_free (map (rpair Term.dummy) frees)) |> map Free
         val prop = gprop |> Logic.dest_implies |> fst |> HOLogic.dest_Trueprop
         val rhs =
           prop
           |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) ((@{thm conj_assoc} |> meta_eq) :: subs) []
           |> subst_free (frees ~~ frees') |> HOLogic.tupled_lambda (HOLogic.mk_tuple frees')
         val lhs = prop |> lambda (HOLogic.mk_tuple frees |> wrap_id_)
       in
         if lhs aconv rhs then []
         else
           [Goal.prove ctxt [] [] (HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop)
             (HEADGOAL
               (rewrite_goal_tac ctxt (map meta_eq [@{thm split_beta'}, @{thm conj_assoc}])
                THEN' resolve_tac ctxt [@{thm refl}]) |> K) |> meta_eq]
       end
    in
      instantiate_normalize u gthm \<comment> \<open>(6)\<close>
      |> rewrite_rule ctxt subs |> curry op RS intro \<comment> \<open>(7)\<close>
      |> rewrite_rule ctxt (@{thm id__def} :: eps_simps) |> Drule.generalize gens |> zero_var_indexes \<comment> \<open>(8)\<close>
    end
  fun dest_premise ctxt ethm =
    let
      val prem = ethm |> Thm.prems_of |> hd
      val fix_typ = map_type_tvar (TFree o apfst fst)
      val vars = Logic.strip_params prem |> map (apfst (maybe_skolem ctxt) ##> fix_typ)
      val chyps =
        Logic.strip_assums_hyp prem
        |> map (pair (vars |> rev |> map Free) #> subst_bounds #> map_types fix_typ #> Thm.cterm_of ctxt)
    in
      (vars, chyps)
    end
  fun export ctxt ethm thm =
    let
      val (vars, chyps) = dest_premise ctxt ethm
      val idx = Thm.maxidx_of thm + 1
      val prop = Thm.prop_of thm
      val prop' =
        prop
        |> map_aterms
          (fn Free (v, T) =>
            if member (op = o apsnd fst) vars v
            then Var ((v, idx), T)
            else Free (v, T) | t => t)
        |> map_types (map_type_tfree (fn (t, S) => TVar ((t, idx), S)))
      val thm = rewrite_rule ctxt [@{thm prop_def}] thm
      val athm =
        if inter (op =) vars (Term.add_frees prop []) |> null
        then
          thm |> Conv.fconv_rule (Object_Logic.atomize ctxt)
          |> fold_rev Thm.implies_intr chyps
          |> Drule.generalize ([], map fst vars)
          |> rpair ethm |> op CCOMP
        else export0 ctxt vars chyps thm CCOMP ethm
    in
      Goal.prove ctxt [] [] prop'
        (HEADGOAL
          (rewrite_goal_tac ctxt [@{thm prop_def}]
           THEN' Object_Logic.full_atomize_tac ctxt
           THEN' resolve_tac ctxt [athm]) |> K)
    end
  fun export_term ctxt ethm =
    Thm.cterm_of ctxt #> Thm.reflexive
    #> export ctxt ethm
    #> Thm.prop_of #> Logic.dest_equals #> fst
  fun guess ctxt' ctxt (thm, pos) facts =
    let
      val thm = singleton (Attrib.eval_thms ctxt') thm
      val ethm = List.foldl (op CCOMP) thm facts
      val binds = Rule_Cases.get thm |> fst |> the_single |> fst |> snd
      val (vars, hyps) = dest_premise ctxt ethm |>> map (maybe_dest_skolem ctxt |> apfst) ||> map Thm.term_of
      fun exports _ _ = (export ctxt ethm, export_term ctxt ethm)
      val fixes = vars |> map (apfst (rpair pos #> Binding.make) #> apsnd SOME #> rpair NoSyn #> Scan.triple1)
      val assms =
        binds ~~ hyps |> map (apsnd (rpair []) ##> single #>> rpair pos #>> Binding.make #>> Thm.no_attributes)
    in
      { exports = exports, fixes = fixes, assms = assms }
    end
  fun hilbert_guess_meth thm_pos ctxt' facts (ctxt, st) =
    let
      val { exports, fixes, assms } = guess ctxt' ctxt thm_pos facts
    in
      ctxt
      |> Proof_Context.add_fixes fixes |> snd
      |> Proof_Context.add_assms exports assms |> snd
      |> rpair st |> Seq.succeed |> Seq.make_results
    end
    handle ListPair.UnequalLengths => Seq.single (Seq.Error (fn () => "No enough chained facts or hyp names"))
  fun guess_from_rule_cmd thm_pos state =
    let
      val ctxt = Proof.context_of state
      val facts = if can Proof.assert_chain state then Proof.the_facts state else []
      val { exports, fixes, assms } = guess ctxt ctxt thm_pos facts
    in
      state
      |> Proof.assert_forward_or_chain
      |> Proof.enter_forward
      |> Proof.fix fixes
      |> Proof.assm exports [] [] assms
    end
  fun rule_context_cmd thm_pos lthy =
    let
      val { exports, fixes, assms } = guess lthy lthy thm_pos []
      val abbrevs =
        fixes |> map (fn (b, typ, mx) => ((b, mx), Free (Binding.name_of b, the typ) |> snd (exports false [])))
      val notes = assms |> map (map (fst #> Thm.cterm_of lthy #> Thm.assume #> fst (exports false [])) |> apsnd)
      fun abbreviate a =
        Local_Theory.abbrev Syntax.mode_default a #> snd #>
        (fn lthy =>
          Local_Theory.map_contexts
            (Proof_Context.revert_abbrev
              "" (Binding.name_of (a |> fst |> fst) |> Long_Name.qualify (Named_Target.locale_of lthy |> the)) |> K)
            lthy)
    in
      lthy
      |> fold abbreviate abbrevs
      |> fold (snd oo Local_Theory.note) notes
    end
  val meth : (Proof.context -> Method.method) context_parser =
    Scan.lift (Parse.position Parse.thm) >> hilbert_guess_meth
  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>guess_by_rule\<close> "wild guessing using an elimination rule"
      (Parse.position Parse.thm >> (Toplevel.proof o guess_from_rule_cmd))
  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>rule_context\<close> "intoducing declarations from an elimination rule"
      (Parse.position Parse.thm >> (Toplevel.local_theory NONE NONE o rule_context_cmd))
end
\<close>

method_setup hilbert_guess = \<open>Hilbert_Guess.meth\<close> "Elimination into local context"

thm wf_asym wfE_min bij_pointE finite_subset_Union int_diff_cases zip_eq_ConsE prod_cases

lemma wf_asym': assumes wf: "wf R" shows "asym R" proof (intro asymI)
  fix a b assume "(a, b) \<in> R"
  with wf show "(b, a) \<notin> R" apply (hilbert_guess wf_asym[case_names _[asym]]) by (rule asym)
qed

lemma wf_asym'':
  assumes wf: "wf R" and ab: "(a, b) \<in> R"
  shows
    "(b, c) \<in> R \<Longrightarrow> c = a \<Longrightarrow> False"
    "b = c \<Longrightarrow> (c, a) \<in> R \<Longrightarrow> False"
proof-
  presume ba: "(b, a) \<in> R"
  from wf ab show False apply (hilbert_guess wf_asym[case_names _[asym]]) by (rule cnf.clause2raw_notE[OF ba asym])
  thus False .
next
  assume "(b, c) \<in> R" "c = a"
  thus "(b, a) \<in> R" by (elim subst)
next
  assume "b = c" "(c, a) \<in> R"
  thus "(b, a) \<in> R" by (subst (asm) eq_commute) (elim subst)
qed

lemma underE: assumes "y \<in> under R z" obtains "(y, z) \<in> R" using assms unfolding under_def by simp

lemma wf_min:
  assumes wf: "wf R" and nonemp: "x \<in> Q"
  shows "\<exists>z\<in>Q.\<forall>y\<in>under R z. y \<notin> Q"
  using wf nonemp
  apply (hilbert_guess wfE_min[rename_abs z, case_names _[member min]])
proof  (intro bexI[of _ z] ballI impI member)
  fix y assume "y \<in> under R z"
  hence "(y, z) \<in> R" apply (hilbert_guess underE[case_names _[prod]]) by (rule prod)
  thus "y \<notin> Q" by (rule min)
qed

lemma wf_min':
  assumes wf: "wf R" and nonemp: "x \<in> Q"
  shows "\<exists>z\<in>Q.\<forall>y\<in>under R z. y \<notin> Q"
  apply (intro bexI)
  using wf nonemp apply (hilbert_guess wfE_min[rename_abs z, case_names _[member min]])
proof (intro ballI impI)
  fix y assume "y \<in> under R z"
  hence "(y, z) \<in> R" apply (hilbert_guess underE[case_names _[prod]]) by (rule prod)
  thus "y \<notin> Q" by (rule min)
next
  show "z \<in> Q" by (rule member)
qed

schematic_goal wf_min'':
  assumes wf: "wf R" and nonemp: "x \<in> Q"
  shows "?z \<in>Q" "\<forall>y\<in>under R ?z. y \<notin> Q"
  using wf nonemp apply (hilbert_guess wfE_min[case_names _[member min]])
   apply (rule member)
proof (intro ballI impI)
  fix y assume "y \<in> under R z"
  hence "(y, z) \<in> R" apply (hilbert_guess underE[case_names _[prod]]) by (rule prod)
  thus "y \<notin> Q" by (rule min)
qed

lemma bij_point:
  assumes bij: "bij f"
  shows "\<exists>!x. y = f x"
proof (intro ex1I)
  from bij guess_by_rule bij_pointE[where y=y, rename_abs x, case_names _[ex 1]]
  from ex show "y = f x" .
  from 1 show "y = f x'  \<Longrightarrow> x' = x" for x' .
qed

schematic_goal bij_point':
  assumes bij: "bij f"
  shows "y = f ?x" and "\<And> x'. y = f x'  \<Longrightarrow> x' = ?x"
proof-
  from bij guess_by_rule bij_pointE[where y=y, rename_abs x, case_names _[ex 1]]
  from ex show "y = f x" .
  from 1 show "y = f x'  \<Longrightarrow> x' = x" for x' .
qed

lemma bij_point'':
  assumes bij: "bij f"
  shows "\<exists>!x. y = f x"
proof (intro ex1I)
  from bij_pointE bij guess x .
  note Ex = this
  from Ex(1) show "y = f x" oops

lemma finite_subset_Union':
  assumes "finite A" "A \<subseteq> \<Union> \<B>"
  obtains \<F> where "finite \<F>" "\<F> \<subseteq> \<B>" "A \<subseteq> \<Union> \<F>"
proof
  {
    from assms guess_by_rule finite_subset_Union[rename_abs \<F>, case_names _[finite sub subset]]
    thm finite sub subset
    thus "finite \<F>" "\<F> \<subseteq> \<B>" "A \<subseteq> \<Union> \<F>" .
  }
qed

lemma finite_subset_Union'':
  assumes "finite A" "A \<subseteq> \<Union> \<B>"
  obtains \<F> where "finite \<F>" "\<F> \<subseteq> \<B>" "A \<subseteq> \<Union> \<F>"
proof
  {
    from finite_subset_Union assms guess \<F> .
    thus "finite \<F>" "\<F> \<subseteq> \<B>" "A \<subseteq> \<Union> \<F>" oops

lemma int_nats: "\<exists> m n. z = int m - int n"
  apply (intro exI)
  apply (hilbert_guess int_diff_cases[rename_abs m n, of z, case_names _[diff]]) thm diff
  by (rule diff)

lemma ex_tails:
  assumes "zip xs ys = xy # xys"
  obtains xs' ys' where "xys = zip xs' ys'"
proof
  {
    from assms guess_by_rule zip_eq_ConsE[rename_abs _ xs' _ ys', case_names _[_ _ _ tails]]
    from tails show "xys = zip  xs' ys'" .
  }
qed

schematic_goal "(?a, ?b) = x"
proof
  {
    guess_by_rule prod_cases[rename_abs a b, of _ x]
    have "fst (a, b) = fst x \<or> fst (a, b) \<noteq> fst  x" by simp
  }
  oops

locale empty = fixes a :: int  begin
rule_context int_diff_cases[of 5, case_names _[diff]]
lemma u: "m > n" using diff by simp
end

term empty.n
thm empty.u

end
