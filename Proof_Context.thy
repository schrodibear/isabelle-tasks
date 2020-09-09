theory Proof_Context
  imports Main
begin

ML \<open>
infix 0 CCOMPN CCOMP
signature BASIC_UTIL = sig
  val CCOMPN : thm * (int * thm) -> thm
  val CCOMP : thm * thm -> thm
end
structure Util = struct
  fun super_thys (thy1, thy2) =
    if Context.subthy (thy1, thy2) then thy1
    else if Context.subthy (thy2, thy1) then thy2
    else raise THEORY ("No proper supertheory", [thy1, thy2])
  val super_thys_of = apply2 Thm.theory_of_thm #> super_thys
  fun unifiers context max (t1, t2) =
    Unify.unifiers (context, Envir.empty max, [(t1, t2)]) |>
    Seq.map
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
      val thy = super_thys_of (r, s)
      val max = Thm.maxidx_of r + Thm.maxidx_of s + 1
    in
      Logic.get_goal (Thm.prop_of s) i |>
      pair [] |> perhaps (I ##>> Logic.dest_all #>> swap #>> uncurry cons |> try |> perhaps_loop) |>> rev ||>
      pair (Thm.forall_elim_vars 0 r |> Thm.incr_indexes (Thm.maxidx_of s + 1)) ||>
      `(apfst Thm.prop_of #> unifiers (Context.Theory thy) max #> Seq.hd) ||> apsnd fst ||>
      `(uncurry Drule.instantiate_normalize) ||> apsnd (fst o fst) |>
      (fn (vars, (r, tys)) =>
        vars |>
        map (typ_subst_TVars (map (fst |> apfst ##> Thm.typ_of) tys) |> apsnd #> Free #> Thm.global_cterm_of thy) |>
        rpair r |-> Drule.forall_intr_list |>
        rpair (i, s) |> Scan.triple2 |> Drule.compose)
    end
  fun r CCOMP s = r CCOMPN (1, s)
end
structure Basic_Util : BASIC_UTIL = Util
open Basic_Util
\<close>

ML \<open>
structure Hilbert_Guess = struct
  fun meta_eq e = e RS @{thm atomize_eq[THEN equal_elim_rule2]}
  val prod_conv_thms = [@{thm fst_conv}, @{thm snd_conv}] |> map meta_eq
  fun prod_sel_tac ctxt =
    rewrite_goal_tac ctxt prod_conv_thms THEN'
    resolve_tac ctxt [@{thm refl}]
  fun nth_conv ctxt n k =
    let
      val (xs, Ts) =
        ("a", Name.aT) |>
        apply2 (fn s => Name.invent Name.context s n) ||>
        map (fn v => TFree (v, Sign.defaultS \<^theory>))
      val ts = xs ~~ Ts |> map Free
      val t = nth ts (k - 1)
      val (last, m) = if n = k then (HOLogic.mk_snd, n - 2) else (HOLogic.mk_fst, k - 1)
      val lhs = HOLogic.mk_tuple ts |> funpow m HOLogic.mk_snd |> last
    in
      Goal.prove ctxt xs [] (HOLogic.mk_eq (lhs, t) |> HOLogic.mk_Trueprop) (HEADGOAL (prod_sel_tac ctxt) |> K)
    end
  val True_simp = @{lemma "(True \<and> A) = A" by simp} |> meta_eq
  fun conj_elim_tac ctxt =
    REPEAT_ALL_NEW (eresolve_tac ctxt [@{thm conjE}]) THEN'
    assume_tac ctxt
  fun export0 ctxt vars chyps thm =
    let
      val phyps = map Thm.term_of chyps
      val conj =
        phyps |>
        map HOLogic.dest_Trueprop |>
        List.foldl (HOLogic.mk_conj o swap) \<^term>\<open>True\<close> |>
        Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) [True_simp] []
      val pconj = HOLogic.mk_Trueprop conj
      val gens = split_list vars ||> map (fst o dest_TFree) |> swap
      val intros =
        map
          (curry Logic.mk_implies pconj #>
           Thm.cterm_of ctxt #>
           (fn g => HEADGOAL (conj_elim_tac ctxt) |> K |> Goal.prove_internal ctxt [] g) #>
           Drule.generalize gens)
          phyps
      val cconj = Thm.cterm_of ctxt pconj
      val cfrees = map (Thm.cterm_of ctxt o Free) vars
      val n = length vars
      val subs = 1 upto n |> map (nth_conv ctxt n #> meta_eq) |> map (Drule.infer_instantiate' ctxt (map SOME cfrees))
      val gthm = \<comment> \<open>\<open>hyps ?\<^bold>x \<Longrightarrow> G ?\<^bold>x\<close>\<close>
        fold_rev Thm.implies_intr chyps thm |>
        fold (curry op RS (Thm.assume cconj) oo curry op RS) intros |>
        Thm.implies_intr cconj
      val gprop = \<comment> \<open>\<open>hyps (tup \<^bold>x) \<Longrightarrow> G (tup \<^bold>x)\<close>, all local Frees are grouped in the same tuple\<close>
        gthm |>
        Thm.prop_of |>
        subst_free (map (swap o Logic.dest_equals o Thm.prop_of) subs) |>
        Thm.cterm_of ctxt
      val gthm =
        gprop |>
        Goal.init |> HEADGOAL (rewrite_goal_tac ctxt subs) |> Seq.hd |> pair gthm |> op COMP |> Goal.conclude |>
        \<comment> \<open>\<Up> Have proved \<open>gprop\<close> from \<open>gthm\<close>\<close>
        Conv.fconv_rule (Object_Logic.atomize ctxt) |>
        fold Thm.forall_intr cfrees |>
        funpow (n - 1) (op CCOMP o rpair @{thm prod.induct}) |>
        \<comment> \<open>\<Up> Have proved \<open>gprop\<close>, where \<open>?x\<close> is a single Var, \<^emph>\<open>not\<close> a vector\<close>
        rpair @{thm mp} |> op COMP |>
        rpair (2, @{thm someI2}) |> op CCOMPN
        \<comment> \<open>\<Up> Replaced this ?x \<^emph>\<open>in the goal\<close> with \<open>SOME x. hyps (tup x)\<close>, thus eliminating the local dep\<close>
      val u = \<comment> \<open>Simplify \<open>gthm\<close> by instantiating it so its premise unifies with that of original \<open>gprop\<close>\<close>
        (gprop, Thm.cprop_of gthm) |> apply2 (Thm.term_of #> Logic.dest_implies #> fst) |>
        Util.unifiers (Context.Proof ctxt) (Thm.maxidx_of gthm) |> Seq.hd
    in
      Drule.instantiate_normalize u gthm |>
      rewrite_rule ctxt subs |>
      curry op RS @{thm conjI} |>
      Drule.generalize gens |> Drule.zero_var_indexes
    end
  fun dest_premise ctxt ethm =
    let
      val prem = ethm |> Thm.prems_of |> hd
      val fix_typ = map_type_tvar (TFree o apfst fst)
      val vars = Logic.strip_params prem |> map (apfst Name.skolem ##> fix_typ)
      val chyps =
        Logic.strip_assums_hyp prem |>
        map (pair (vars |> rev |> map Free) #> subst_bounds #> map_types fix_typ #> Thm.cterm_of ctxt)
    in
      (vars, chyps)
    end
  fun export ctxt ethm thm =
    let
      val (vars, chyps) = dest_premise ctxt ethm
      val idx = Thm.maxidx_of thm + 1
      val prop =
        Thm.prop_of thm |>
        map_aterms
          (fn Free (v, T) =>
            if member (op = o apsnd fst) vars v
            then Var ((v, idx), T)
            else Free (v, T) | t => t) |>
        map_types (map_type_tfree (fn (t, S) => TVar ((t, idx), S)))
      val athm = export0 ctxt vars chyps thm CCOMP ethm
    in
      Goal.prove ctxt [] [] prop (HEADGOAL (Object_Logic.full_atomize_tac ctxt THEN' resolve_tac ctxt [athm]) |> K)
    end
  fun export_term ctxt ethm =
    Thm.cterm_of ctxt #>
    Thm.reflexive #>
    export ctxt ethm #>
    Thm.prop_of #>
    Logic.dest_equals #>
    fst
  fun hilbert_guess_meth (thm, pos) facts (ctxt, st) =
    let
      val ethm = List.foldl (op CCOMP) thm facts
      val binds = Rule_Cases.get thm |> fst |> the_single |> fst |> snd
      val (vars, hyps) = dest_premise ctxt ethm |>> map (apfst Name.dest_skolem) ||> map Thm.term_of
      fun exprt goal _ =
        let
          fun wrap f = if goal then Goal.conclude #> f #> Goal.protect 0 else f
        in
          (wrap (export ctxt ethm), export_term ctxt ethm)
        end
    in
      ctxt |>
      Proof_Context.add_fixes
        (vars |> map (apfst (rpair pos #> Binding.make) #> apsnd SOME #> rpair NoSyn #> Scan.triple1)) |> snd |>
      Proof_Context.add_assms
        exprt
        (binds ~~ hyps |> map (apsnd (rpair []) ##> single #>> rpair pos #>> Binding.make #>> Thm.no_attributes)) |>
      snd |>
      rpair st |> Seq.succeed |> Seq.make_results
    end
  val meth : (Proof.context -> Method.method) context_parser =
    Scan.lift (Parse.position Parse.thm) >>
      (fn (thm, pos) => fn ctxt => hilbert_guess_meth (singleton (Attrib.eval_thms ctxt) thm, pos))
end
\<close>

method_setup hilbert_guess = \<open>Hilbert_Guess.meth\<close> "Elimination into local context"

declare [[ML_print_depth=200]]

lemma eqsE[case_names Eqs[AB BC]]: obtains A B C where "A = B" "B = C" by simp

schematic_goal U: "D \<Longrightarrow> ?A = ?C"
  apply (hilbert_guess eqsE)
  apply (rule trans[OF AB BC])
  done

lemma G: "(\<lambda> p. F p) = case_prod (\<lambda> x y. F (x, y))" by simp
lemma GG: "PROP Q (SOME x. P x) \<Longrightarrow> PROP Q (SOME (x, y). P (x, y))" by simp

ML \<open> @{thm U} CCOMP @{thm GG}\<close>

ML \<open>\<^term>\<open>SOME (a,b,c). a = b\<close>\<close>

ML \<open>
let
  val vars = ["A",  "B", "C"] |> map (rpair \<^typ>\<open>'a\<close>)
  val subs = vars |> map (`(apfst Name.skolem) #> swap #> apply2 Free)
  val AB = \<^prop>\<open>A = B\<close> |> subst_free subs |> Thm.cterm_of \<^context>
  val BC = \<^prop>\<open>B = C\<close> |> subst_free subs |> Thm.cterm_of \<^context>
  val thmAB = Thm.assume AB
  val thmBC = Thm.assume BC
  val thm = Thm.implies_intr \<^cprop>\<open>D\<close> (@{thm trans} OF [thmAB, thmBC])

in
  Hilbert_Guess.export \<^context> @{thm eqsE} thm
end
\<close>

consts A :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

lemma xx:"A (fst (snd (snd (x, y, z, w)))) (fst (snd (snd (x, y, z, w))))" sorry
lemma yy: "(\<And> a b. P (a, b)) \<Longrightarrow> P p" sorry
ML \<open>@{thm xx} RSN (1, @{thm yy})\<close>

lemma x: "A (fst (snd (snd (x, y, z, w)))) (fst (snd (snd (x, y, z, w))))" sorry
ML \<open>@{thm x} CCOMP @{thm prod.induct} CCOMP @{thm prod.induct}\<close>

ML \<open>Elim.nth_conv \<^context> 5 5\<close>

lemma "z = fst (snd (snd (x, y, z, w)))"  apply (tactic \<open>HEADGOAL (Elim.prod_sel_tac \<^context>)\<close>)

thm subset_imageE
thm someI2

ML \<open>Assumption.add_assms\<close>

lemma set_split[case_names A[t u] B[u t], induct pred]:
  assumes "t \<noteq> u"
  obtains
    (1) x where "x \<in> t" "x \<notin> u" |
    (2) x where "x \<in> u" "x \<notin> t"
  using assms by auto

lemma assumes "s \<noteq> t" shows "\<exists> x. x \<in> s - t \<or> x \<in> t - s" using assms proof induct
  case (A x)
  from A.t have False
qed
end