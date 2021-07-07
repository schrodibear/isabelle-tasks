(*<*)
theory De_Brujin
  imports HOL.Nat
begin
(*>*)
ML \<open>
let
  local
    fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
    fun pp_list xs = Pretty.list "[" "]" xs
    fun pp_str s = Pretty.str s
    fun pp_qstr s = Pretty.quote (pp_str s)
    fun pp_int i = pp_str (string_of_int i)
    fun pp_sort S = pp_list (map pp_qstr S)
    fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
  in
    fun raw_pp_typ (TVar ((a, i), S)) =
         pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
      | raw_pp_typ (TFree (a, S)) =
          pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
      | raw_pp_typ (Type (a, tys)) =
          pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
  end
in
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ)
end\<close>
ML \<open>
  \<^term>\<open>HOL.All (\<lambda> y :: nat. HOL.implies (HOL.Not (HOL.eq y 0)) (Rings.dvd_class.dvd y (Groups.plus_class.plus x d)))\<close>
  |> Term.subst_free [(\<^term>\<open>x :: nat\<close>, Var (("x", 0), \<^typ>\<open>nat\<close>))]\<close>
ML \<open>
  \<^term>\<open>All (\<lambda> y :: nat. implies (Not (eq y 0)) (dvd_class.dvd y (plus x d)))\<close>
  |> Term.subst_free [(\<^term>\<open>x :: nat\<close>, Var (("x", 0), \<^typ>\<open>nat\<close>))]\<close>
ML \<open>
  \<^term>\<open>\<forall>y :: nat \<noteq> 0. y dvd (x + d) * y\<close>
  |> Term.subst_free [(\<^term>\<open>x :: nat\<close>, Var (("x", 0), \<^typ>\<open>nat\<close>))]\<close>

term "\<forall>y :: nat \<noteq> 0. y dvd (x + d) * y"

abbreviation (output) "All_neq y P \<equiv> \<forall>x. x \<noteq> y \<longrightarrow> P x"
translations "\<forall>x\<noteq>y. P" \<leftharpoondown> "CONST All_neq y (\<lambda> x. P)"
term "\<forall>y :: nat \<noteq> 0. y dvd (x + d) * y"

(*<*)
end
(*>*)
