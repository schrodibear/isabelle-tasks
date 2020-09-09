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
      (fn (Envir.Envir { tyenv, tenv, ... }, _) =>
        (tyenv |> Vartab.dest |>
         map (fn (xi, (S, T)) => ((xi, S), Context.cases Thm.global_ctyp_of Thm.ctyp_of context T)),
         tenv |> Vartab.dest |>
         map
           (fn (xi, (T, t)) =>
             ((xi, Envir.subst_type tyenv T),
              Envir.subst_term (tyenv, tenv) t |> Context.cases Thm.global_cterm_of Thm.cterm_of context))))
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
structure Elim_Obtain = struct
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
  fun export ctxt vars chyps thm =
    let
      val phyps = map Thm.term_of chyps
      val conj =
        phyps |>
        map HOLogic.dest_Trueprop |>
        List.foldl (HOLogic.mk_conj o swap) \<^term>\<open>True\<close> |>
        Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) [True_simp] []
      val pconj = HOLogic.mk_Trueprop conj
      val intros =
        map
          (curry Logic.mk_implies pconj #>
           (fn g => HEADGOAL (conj_elim_tac ctxt) |> K |> Goal.prove ctxt (map fst vars) [] g))
          phyps
      val cconj = Thm.cterm_of ctxt pconj
      val cfrees = map (Thm.cterm_of ctxt o Free) vars
      val n = length vars
      val convs = 1 upto n |> map (nth_conv ctxt n #> meta_eq)
      val subs = map (Drule.infer_instantiate' ctxt (map SOME cfrees)) convs
      val gthm = \<comment> \<open>\<open>hyps ?\<^bold>x \<Longrightarrow> G ?\<^bold>x\<close>\<close>
        fold_rev Thm.implies_intr chyps thm |>
        fold (curry op RS (Thm.assume cconj) oo curry op RS) intros |>
        Thm.implies_intr cconj
      val gprop = \<comment> \<open>\<open>hyps (tup \<^bold>x) \<Longrightarrow> G (tup \<^bold>x)\<close>, all local Frees are grouped in the same tuple\<close>
        gthm |>
        Thm.prop_of |>
        Term.subst_free (map (swap o Logic.dest_equals o Thm.prop_of) subs) |>
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
      rewrite_rule ctxt convs |>
      curry op RS @{thm conjI} |>
      Drule.generalize (map (fst o Term.dest_TFree o snd) vars, map fst vars) |> Drule.zero_var_indexes
    end
  structure Rule = Proof_Data (type T = thm option val init = K NONE)
end
\<close>

declare [[ML_print_depth=200]]

ML \<open>
let
  val AB = \<^cprop>\<open>A = B\<close>
  val BC = \<^cprop>\<open>B = C\<close>
  val thmAB = Thm.assume AB
  val thmBC = Thm.assume BC
  val thm = Thm.implies_intr \<^cprop>\<open>D\<close> (@{thm trans} OF [thmAB, thmBC])
  val vars = ["A",  "B", "C"] |> map (rpair \<^typ>\<open>'a\<close>)
in
  Elim_Obtain.export \<^context> vars [AB, BC] thm
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