theory Bypass_Translations
  imports Main
begin

ML \<open>
signature BYPASS_TRANSLATIONS = sig
  val bypass_translations : bool Config.T
  val setup_bypass_translations : theory -> theory
end

structure Bypass_Translations : BYPASS_TRANSLATIONS = struct
  val bypass_prefix = "@"
  val (bypass_translations, setup_bypass_translations) = Attrib.config_bool \<^binding>\<open>bypass_translations\<close> (K false)
  fun bypass ctxt ts =
    if
      Config.get ctxt bypass_translations |> not orelse
      fold (fold_aterms (fn Const (c, _) => (fn acc => acc orelse String.isPrefix bypass_prefix c) | _ => I)) ts false
    then ts
    else
      map
        (map_aterms
          (fn t as Const (c, T) =>
                if strip_type T |> swap |-> cons |> forall (curry op <> \<^typ>\<open>prop\<close>) then
                  Const (prefix bypass_prefix c, T)
                else t
            | t => t))
        ts
   val () = Syntax_Phases.term_uncheck 101 "bypass all translations" bypass |> Context.>>

local
  open Ast
  fun detect (Constant c) = String.isPrefix bypass_prefix (perhaps (try Lexicon.unmark_const) c)
    | detect (Variable _) = false
    | detect (Appl l) = exists detect l
  fun restore (Constant c) =
        Constant (perhaps (try (Lexicon.unmark_const #> unprefix bypass_prefix #> Lexicon.mark_const)) c)
    | restore (v as Variable _) = v
    | restore (Appl l) = Appl (map restore l)
in
  val () =
    Sign.print_ast_translation
      [(\<^const_syntax>\<open>Trueprop\<close>,
        fn ctxt => fn args =>
          if Config.get ctxt bypass_translations andalso exists detect args then
            Ast.mk_appl (Ast.Constant \<^const_syntax>\<open>Trueprop\<close>) (map restore args)
          else raise Match)]
    |> Context.map_theory |> Context.>>
end
end
\<close>
setup \<open>Bypass_Translations.setup_bypass_translations\<close>

abbreviation (output) "Sum_list f xs \<equiv> sum_list (map f xs)"
print_translation \<open>[Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>Sum_list\<close> \<^const_syntax>\<open>Sum_list\<close>]\<close>
translations "\<Sum>x\<leftarrow>xs. b" \<leftharpoondown>"CONST Sum_list x b xs"

lemma "{u. P u} = {(a, b) | a b. P (a, b)}" using [[show_abbrevs=false, bypass_translations=true]] oops

prop "finite X \<Longrightarrow> (\<Sum>x\<in>X. \<Sum>y\<leftarrow>ys. f x y) = (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>X. f x y)"
prop "{u. P u} = {(a, b) | a b. P (a, b)}"

declare [[show_abbrevs=false, bypass_translations=true]]

prop "finite X \<Longrightarrow> (\<Sum>x\<in>X. \<Sum>y\<leftarrow>ys. f x y) = (\<Sum>y\<leftarrow>ys. \<Sum>x\<in>X. f x y)"
prop "{u. P u} = {(a, b) | a b. P (a, b)}"

end
