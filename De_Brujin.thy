(*<*)
theory De_Brujin
  imports HOL.Nat
begin
(*>*)
ML \<open>
  \<^term>\<open>HOL.All (\<lambda> y :: nat. HOL.implies (HOL.Not (HOL.eq y 0)) (Rings.dvd_class.dvd y (Groups.plus_class.plus x d)))\<close>
  |> Term.subst_free [(\<^term>\<open>x :: nat\<close>, Var (("x", 0), \<^typ>\<open>nat\<close>))]\<close>
ML \<open>
  \<^term>\<open>\<forall>y :: nat \<noteq> 0. y dvd (x + d)\<close>
  |> Term.subst_free [(\<^term>\<open>x :: nat\<close>, Var (("x", 0), \<^typ>\<open>nat\<close>))]\<close>
(*<*)
end
(*>*)
