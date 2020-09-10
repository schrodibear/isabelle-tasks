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
      pair (Thm.forall_elim_vars (Thm.maxidx_of s + 1) r) ||>
      `(apfst Thm.prop_of #> unifiers (Context.Theory thy) max #> Seq.hd) ||> apsnd fst ||>
      `(uncurry Drule.instantiate_normalize) ||> apsnd (fst o fst) |>
      (fn (vars, (r, tys)) =>
        vars |>
        map (typ_subst_TVars (map (fst |> apfst ##> Thm.typ_of) tys) |> apsnd #> Free #> Thm.global_cterm_of thy) |>
        rpair r |-> Drule.forall_intr_list |>
        rpair (i, s) |> Scan.triple2 |> Drule.compose |> Drule.zero_var_indexes)
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
  pair (\<^binding>\<open>id__def\<close>, \<^term>\<open>I x \<equiv> x\<close> |> subst_free [(\<^term>\<open>I :: 'a \<Rightarrow> 'a\<close>, Util.id_ \<^typ>\<open>'a\<close>)]) #>>
  Thm.simple_fact #->
  Global_Theory.add_defs false #>
  snd
\<close>

ML \<open>
structure Hilbert_Guess = struct
  fun meta_eq e = e RS @{thm atomize_eq[THEN equal_elim_rule2]}
  val prod_conv_thms = [@{thm fst_conv}, @{thm snd_conv}] |> map meta_eq
  fun prod_sel_tac ctxt =
    rewrite_goal_tac ctxt prod_conv_thms THEN'
    resolve_tac ctxt [@{thm refl}]
  fun wrap t = Util.id_ (type_of t) $ t
  fun nth_conv ctxt n k =
    let
      val (xs, Ts) =
        ("a", Name.aT) |>
        apply2 (fn s => Name.invent Name.context s n) ||>
        map (fn v => TFree (v, Sign.defaultS \<^theory>))
      val ts = xs ~~ Ts |> map Free
      val t = nth ts (k - 1)
      val (last, m) = if n = k then (HOLogic.mk_snd, n - 2) else (HOLogic.mk_fst, k - 1)
      val lhs = HOLogic.mk_tuple ts |> wrap |> funpow m HOLogic.mk_snd |> last
    in
      Goal.prove ctxt xs [] (HOLogic.mk_eq (lhs, t) |> HOLogic.mk_Trueprop)
        (HEADGOAL (rewrite_goal_tac ctxt [@{thm id__def}] THEN' prod_sel_tac ctxt) |> K)
    end
  val nth_conv = fn ctxt => fn n => if n = 1 then K @{thm refl} else nth_conv ctxt n
  val True_simp = @{lemma "(True \<and> A) = A" by simp} |> meta_eq
  fun conj_elim_tac ctxt =
    REPEAT_ALL_NEW (eresolve_tac ctxt [@{thm conjE}]) THEN'
    assume_tac ctxt
  fun export0 ctxt vars chyps thm =
    let
      val gens = split_list vars ||> map (fst o dest_TFree) |> swap
      val gthm = \<comment> \<open>\<open>H ?\<^bold>x \<Longrightarrow> G ?\<^bold>x\<close>, \<open>H\<close> is a single conjunction of \<open>chyps\<close>, \<open>G\<close> is \<open>thm\<close>\<close>
        let
          val phyps = map Thm.term_of chyps
          val pconj =
            phyps |>
            map HOLogic.dest_Trueprop |>
            List.foldl (HOLogic.mk_conj o swap) \<^term>\<open>True\<close> |>
            Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) [True_simp] [] |>
            HOLogic.mk_Trueprop
          val intros =
            map
              (curry Logic.mk_implies pconj #>
               Thm.cterm_of ctxt #>
               (fn g => HEADGOAL (conj_elim_tac ctxt) |> K |> Goal.prove_internal ctxt [] g) #>
               Drule.generalize gens)
              phyps
          val cconj = Thm.cterm_of ctxt pconj
        in
          fold_rev Thm.implies_intr chyps thm |>
          fold (curry op RS (Thm.assume cconj) oo curry op RS) intros |>
          Thm.implies_intr cconj
        end
      val frees = map Free vars
      val cfrees = map (Thm.cterm_of ctxt) frees
      val n = length vars
      val subs = 1 upto n |> map (nth_conv ctxt n #> meta_eq) |> map (Drule.infer_instantiate' ctxt (map SOME cfrees))
      val gprop = \<comment> \<open>\<open>H (tup \<^bold>x) \<Longrightarrow> G (tup \<^bold>x)\<close>, all local Frees are grouped in the same tuple\<close>
        gthm |>
        Thm.prop_of |>
        subst_free (map (swap o Logic.dest_equals o Thm.prop_of) subs)
      fun induct k =
        let
          val m = n - k - 1
          val sub = HOLogic.mk_tuple (drop m frees)
          val x = Term.variant_frees gprop [("x", type_of sub)] |> the_single
          val subs = apply2 (fn x => take m frees @ [x] |> HOLogic.mk_tuple |> wrap) (sub, Free x) |> single
        in
          gprop |>
          Object_Logic.atomize_term ctxt |>
          Pattern.rewrite_term (Proof_Context.theory_of ctxt) subs [] |>
          lambda (Free x) |> Thm.cterm_of ctxt |> SOME |> single |>
          rpair @{thm prod.induct} |-> Drule.infer_instantiate' ctxt |>
          Drule.generalize gens
        end
      val gthm =
        Goal.prove_internal ctxt [] (Thm.cterm_of ctxt gprop)
          (HEADGOAL (rewrite_goal_tac ctxt subs THEN' solve_tac ctxt [gthm]) |> K) |>
        \<comment> \<open>\<Up> Have proved \<open>gprop\<close> from \<open>gthm\<close>\<close>
        Conv.fconv_rule (Object_Logic.atomize ctxt) |>
        fold_rev Thm.forall_intr cfrees |>
        fold (fn n => fn thm => thm CCOMP induct n) (1 upto n - 1) |>
        \<comment> \<open>\<Up> Have proved atomized \<open>gprop\<close>, where \<open>?x\<close> is a single Var, \<^emph>\<open>not\<close> a vector\<close>
        rpair @{thm mp} |> op COMP |>
        rpair (2, @{thm someI2}) |> op CCOMPN
        \<comment> \<open>\<Up> Replaced this ?x \<^emph>\<open>in the goal\<close> with \<open>SOME x. hyps (tup x)\<close>, thus eliminating the local dep\<close>
     val u = \<comment> \<open>Instantiate \<^emph>\<open>premises\<close> of \<open>gthm\<close> with the original tuple of fixed variables\<close>
        (gprop, Thm.prop_of gthm) |> apply2 (Logic.dest_implies #> fst) |>
        Util.unifiers (Context.Proof ctxt) (Thm.maxidx_of gthm) |> Seq.hd
     val eps_simp =
       let
         val vars' = map (apfst Name.dest_skolem) vars
         val frees' =
           vars' |>
           Term.variant_frees (gprop |> subst_free (map (rpair Term.dummy) frees)) |>
           map Free
         val prop = gprop |> Logic.dest_implies |> fst |> HOLogic.dest_Trueprop
         val rhs =
           prop |>
           Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) ((@{thm conj_assoc} |> meta_eq) :: subs) [] |>
           subst_free (frees ~~ frees') |>
           HOLogic.tupled_lambda (HOLogic.mk_tuple frees')
         val lhs = prop |> lambda (HOLogic.mk_tuple frees |> wrap)
       in
         Goal.prove ctxt [] [] (HOLogic.mk_eq (lhs, rhs) |> HOLogic.mk_Trueprop)
           (HEADGOAL
             (rewrite_goal_tac ctxt (map meta_eq [@{thm split_beta'}, @{thm conj_assoc}]) THEN'
              resolve_tac ctxt [@{thm refl}]) |> K) |>
         meta_eq
       end
    in
      Drule.instantiate_normalize u gthm |>
      rewrite_rule ctxt subs |>
      funpow (length chyps - 1) (curry op RS @{thm conjI}) |>
      rewrite_rule ctxt [@{thm id__def}, eps_simp] |>
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
          fun wrap f = if goal then fn thm => Goal.conclude thm |> f |> Goal.protect (Thm.nprems_of thm) else f
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

lemma eqsE[case_names Eqs[AB BC Z]]: obtains A B C where "A = B" "B = C" "0 = 0" by simp

schematic_goal U: "D \<Longrightarrow> ?A = ?C"
  apply (hilbert_guess eqsE)
  apply (rule trans[OF AB BC])
  done

lemma G: "(\<lambda> p. F p) = case_prod (\<lambda> x y. F (x, y))" by simp
lemma GG: "(SOME x. P x) = (SOME (x, y). P (x, y))" by simp

lemmas t = U[simplified G]

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