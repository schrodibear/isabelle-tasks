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
  fun unifiers context (t1, t2) =
    Unify.unifiers (context, Envir.init, [(t1, t2)]) |>
    Seq.map
      (fst #>
        (fn Envir.Envir { maxidx, tyenv, tenv } =>
          Envir.Envir
            { maxidx = maxidx,
              tyenv = tyenv,
              tenv =
                Vartab.map
                  (Envir.subst_type tyenv |> apfst ##> Envir.subst_term (tyenv, tenv) |> K)
                  tenv}) #>
       `Envir.type_env ##>>
       `Envir.term_env #>
       fst #>>
       (Vartab.dest #> map (fn (xi, (S, T)) => ((xi, S), T))) ##>
       (Vartab.dest #> map (fn (xi, (T, t)) => ((xi, T), t))) #>>
       map (Context.cases Thm.global_ctyp_of Thm.ctyp_of context |> apsnd) ##>
       map (Context.cases Thm.global_cterm_of Thm.cterm_of context |> apsnd))
  fun r CCOMPN (i, s) =
    Logic.get_goal (Thm.prop_of s) i |>
    pair [] |>
    perhaps (I ##>> Logic.dest_all #>> swap #>> uncurry cons |> try |> perhaps_loop) |>>
    rev |>
    (fn (vars, t) =>
      let
        val r = Thm.forall_elim_vars 0 r
        val thy = super_thys_of (r, s)
        val context = Context.Theory thy
      in
        case unifiers context (Thm.prop_of r, t) |> Seq.chop 2 of
            ([], _) => raise THM ("CCOMPN: no unifiers", 0, [r, s])
          | ((u as (tys, _)) :: _, _) =>
              Drule.instantiate_normalize u r |>
              pair
                (vars |>
                 map
                  (typ_subst_TVars (map (fst |> apfst ##> Thm.typ_of) tys) |> apsnd #>
                   Free #>
                   Thm.global_cterm_of thy)) |->
              Drule.forall_intr_list |>
              rpair (i, s) |>
              Scan.triple2 |>
              Drule.compose
      end)
  fun r CCOMP s = r CCOMPN (1, s)
end
structure Basic_Util : BASIC_UTIL = Util
open Basic_Util
\<close>

thm subset_imageE
thm someI

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