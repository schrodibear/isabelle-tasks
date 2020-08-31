(*<*)
theory Theory_Defs
  imports Pure
begin
(*>*)

section \<open>Inner syntax, type and constant declarations, axiomatization\<close>

subsection \<open>Isabelle/ML interfaces\<close>

text \<open>
  \marginsymbol
  \<^ML_text>\<open>datatype mixfix =
  NoSyn |
  Mixfix of Input.source * int list * int * Position.range |
  Infix of Input.source * int * Position.range |
  Infixl of Input.source * int * Position.range |
  Infixr of Input.source * int * Position.range |
  Binder of Input.source * int * int * Position.range |
  Structure of Position.range\<close>\\
  The most basic datatype underlying the parsing mechanism of Isabelle \<^emph>\<open>inner syntax\<close>. Isabelle theories
  \<^emph>\<open>do not\<close> have any \<^emph>\<open>fixed\<close> syntax defined once and forall, therefore \<^emph>\<open>neither\<close> Isabelle/Isar nor the inner
  language of Isabelle logical terms are by themselves fully defined formal languages. Instead, there are two distinct
  \<^emph>\<open>extensible\<close> parsing \<^emph>\<open>mechanisms\<close> involved in the \<^emph>\<open>incremental\<close> definition of both languages that happens
  along with the development of Isabelle logical theories. So, there are \<^emph>\<open>two\<close> distinct lexing and parsing mechanisms
  involved in defining the languages of Isabelle theory files, namely the \<^emph>\<open>outer\<close> and the \<^emph>\<open>inner\<close> syntaxes:
  \<^item> The \<^emph>\<open>outer syntax\<close> is the syntax of Isabelle theories themselves that actually \<^emph>\<open>do not\<close> form a proper hierarchical
    structure as it may seem from the perspective of a non-expert end-user. Instead, an Isabelle theory is just a
    \<^emph>\<open>stream\<close> of \<^emph>\<open>toplevel commands\<close> that are interpreted sequentially and act on a common shared state describing
    the current theory context. Each command has \<^emph>\<open>its own\<close> syntax defined using a combinatorial parser constructed
    using the primitives defined in modules \<^ML_structure>\<open>Scan\<close> (\<^file>\<open>~~/src/Pure/General/scan.ML\<close>),
    \<^ML_structure>\<open>Parse\<close> (\<^file>\<open>~~/src/Pure/Isar/parse.ML\<close>) and \<^ML_structure>\<open>Args\<close> (\<^file>\<open>~~/src/Pure/Isar/args.ML\<close>). All the
    parsers, though, share a \<^emph>\<open>common lexer\<close>, which may be extended \<^emph>\<open>only once per theory\<close>, namely upon starting a
    new theory by adding a \<^theory_text>\<open>keywords\<close> section in its header. We won't discuss the outer syntax in great detail since
    the corresponding mechanisms and practices are quite common in the realm of functional programming in general and
    have a lot of close analogues in many functional languages other than Isabelle/ML (see OCaml's Angstrom or
    Haskell's parsec for grasping the general idea). We only mention here that Isabelle/ML's parser combinators operate
    on \<^emph>\<open>pairs\<close> with the \<^emph>\<open>second\<close> component representing the abstract stream (actually, a list) of tokens with or
    without the corresponding context. \<^emph>\<open>Context-dependant\<close> parsers operate on a pair of a context and a token stream,
    the stream being the \<^emph>\<open>second\<close> component. Thus the types\\
    \<^ML_text>\<open>type 'a parser = T list -> 'a * T list\<close>\\
    and\\
    \<^ML_text>\<open>type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list)\<close>.\\
  \<^item> The \<^emph>\<open>inner syntax\<close>, however, is defined by somewhat more Isabelle/specific and less well-known means. The inner
    syntax definition has 5 separate stages (\<^bold>\<open>!\<close>). Let's briefly describe them:
    \<^item> \<^emph>\<open>Lexing\<close> stage. At this stage the initial string representing the inner Isabelle logic term and already
      \<^emph>\<open>delimited\<close> by the outer theory syntax is separated into a list of \<^emph>\<open>tokens\<close>. The lexer is mostly
      pre-defined and can \<^emph>\<open>only\<close> be extended \<^emph>\<open>implicitly\<close> by adding so-called \<^emph>\<open>separators\<close> of the \<^emph>\<open>mixfix\<close>
      parsing and printing annotations as well as \<^emph>\<open>constant\<close> names. Those separators are just the tokens corresponding
      to would-be \<^emph>\<open>terminal\<close> symbols of an extensible context-free grammar. There are several pre-defined terminals,
      most importantly, the \<^emph>\<open>identifier\<close> terminal that corresponds to constants and other logical symbols with
      a fixed interpretation and the \<^emph>\<open>variable\<close>, corresponding to uninterpreted symbols. In general, the means to
      extend the inner lexer available to the Isablle/ML user/expert are defining a new constant name and
      defining a new mixfix separator.
    \<^item> \<^emph>\<open>Parsing\<close> stage. At this stage the readily separated list of tokens (Isabelle inner syntax parser is generally
      \<^emph>\<open>not\<close> lazy, so it's possible to handle the entire inner logical term or even several closely related terms
      at once) is transformed into the \<^emph>\<open>untyped AST\<close> defined as follows:\\
      \<^ML_text>\<open>datatype ast =
  Constant of string |
  Variable of string |
  Appl of ast list\<close>\\
      This is a very simple initial AST that, however, already distinguishes \<^emph>\<open>constants\<close> and \<^emph>\<open>variables\<close>. The type
      annotations and binders (particularly, the lambda abstractions) are
      \<^emph>\<open>not yet separated from terms\<close> and are expressed using special constants \<open>_constrain\<close>, \<open>_abs\<close>,
      \<open>_sort_constraint\<close> etc. The only externally available way to extend the parser is by defining a mixfix annotation
      for a constant symbol (say, \<open>c\<close>), thus extending the \<^emph>\<open>context-free grammar\<close> of the inner syntax with a rule
      for producing an AST construct of the form \<open>Appl [Constant c, \<dots>]\<close>. Mixfix annotations are just special
      restricted shortcuts for encoding of grammar rules. In general, a mixfix annotation is just a triple of
      a constant name \<open>c\<close>, a \<^emph>\<open>priority level\<close> \<open>p\<close> and sequence \<open>x\<^sub>1x\<^sub>2\<dots>x\<^sub>n\<close> of the
      following chunks (\<open>xsymb\<close>s, see module \<^ML_structure>\<open>Syntax_Ext\<close>, \<^file>\<open>~~/src/Pure/Syntax/syntax_ext.ML\<close>):\\
      \<^ML_text>\<open>datatype xsymb =
  Delim of string |
  Argument of string * int |
  Space of string |
  Bg of block_info |
  Brk of int |
  En\<close>\\
      Here \<^ML>\<open>Syntax_Ext.Delim\<close> corresponds to a \<^emph>\<open>delimiter\<close> or \<^emph>\<open>separator\<close> that is parsed as a \<^emph>\<open>terminal\<close> token
      distinct both from a constant and a variable. \<^ML>\<open>Syntax_Ext.Argument\<close> represents a \<^emph>\<open>non-terminal\<close> from a
      \<^emph>\<open>fixed selection\<close> of levelled no-terminals i.\,e. pairs of the form \<open>(nonterm, level)\<close> or \<open>nonterm\<^bsup>(level)\<^esup>\<close>, where
      \<open>nonterm\<close> is an identifier, usually representing a general context such as \<open>logic\<close> for terms, \<open>type\<close> for
      types or \<open>sort\<close> for sorts and \<open>level\<close> is a \<^emph>\<open>priority level\<close> ranging from \<open>0\<close> to \<open>1000\<close>. The grammar is formed
      by combining an initial pre-defined basic grammar of Pure logic with those extensions representing rules of the
      form \<open>C\<^bsup>(p)\<^esup> \<leftarrow> d\<^sub>1a\<^sub>1d\<^sub>2\<dots>d\<^sub>ma\<^sub>n (\<Rightarrow> c (a\<^sub>1, \<dots>, a\<^sub>n)\<close>, where \<open>C\<close> is the general context (\<open>logic\<close> or \<open>type\<close>), \<open>p\<close> is the
      priority, the sequence \<open>d\<^sub>1a\<^sub>1d\<^sub>2\<dots>d\<^sub>ma\<^sub>n\<close> is the one provided in the mixfix annotation,
      and the generated AST is of the form \<open>Appl [Constant c, a\<^sub>1, \<dots>, a\<^sub>n]\<close>, as well as the implicit priority
      conversion rules of the form \<open>C\<^bsup>(p-1)\<^esup> \<leftarrow> C\<^bsup>(p)\<^esup>\<close>. Other than that, the grammar is then handled using a general
      Earley parser that is able to produce all possible parsing results (sentences), returned as untyped ASTs,
      for a given sequence of input tokens. Other constructors of the type \<^ML_type>\<open>Syntax_Ext.xsymb\<close>
      represent pretty-printing and formatting annotations and are well described in
      the Isabelle reference manual.
    \<^item> \<^emph>\<open>AST translation\<close> stage. This stage is a rather simple intermediate stage primarily used to define
      more complex syntactic constructs based on the initial simple untyped AST. The most essential aspect of this
      parsing stage is its \<^emph>\<open>untyped\<close> nature. This allows for a free-form transformations of the AST disregarding the
      scope and type restrictions. For example, this way we can define an alternative nice syntax for a lambda binder
      used in a particular context, such as \<open>\<Sigma> i \<in> S. f i\<close>, which should be parsed as \<open>\<Sigma> S (\<lambda> i. f i)\<close>. Here we
      entirely change the way the inner expression \<open>f i\<close> will be parsed further down the pipeline,
      as the occurrences of the variable \<open>i\<close> will now be recognized as \<^emph>\<open>bound\<close> and encoded with de Bruijn indices,
      while, say, potential occurrences of \<open>i\<close> in \<open>S\<close> will be recognized as \<^emph>\<open>free\<close>. In fact, most free-form
      user-defined translations are produced by the command @{command translations}, which defines the rules for
      the transformation of the untyped AST. Now one another very important notice:
      Untyped translations are attached to \<^emph>\<open>constants\<close> and are applied to the resulting AST
      \<^emph>\<open>from left to right\<close> \<^emph>\<open>until a fix-point\<close> is reached i.\,e. there are no more translations defined for any
      of the constants occurring in the AST. The reasons for that are purely pragmatic as this makes it very
      easy to program different transformations with unbound number of arguments, such as various syntaxes for
      lists, sets, records, currified function applications etc. Therefore the translations \<^emph>\<open>should not\<close> normally
      produce output AST constructs that can be matched again by the same translations. For that reason Isabelle
      commonly uses a special notion of a \<^emph>\<open>syntatic constant\<close> that is a special helper constant that is \<^emph>\<open>only\<close> used
      in the untyped AST and is then immediately translated into the actual constant, thus ensuring the corresponding
      translation rule is not applicable anymore. Syntactic constant named usually start with an either an underscore
      or a special control prefix such as \<open>\<^const>\<close> or \<open>\<^typ>\<close>.
    \<^item> \<^emph>\<open>Term translation\<close> stage. Interestingly, this parsing stage is \<^emph>\<open>also untyped\<close>. However, the AST is already
      represented using the usual general \<^ML_type>\<open>term\<close> datatype of Isabelle/Pure. In particular, type constraints
      are still represented using the special constant \<open>_constraint\<close> and the actual types are replaced with dummy
      placeholders (\<^ML>\<open>Term.dummyT\<close>). The term translations (a.k.a simply \<open>parse translations\<close>) are also attached to
      constant symbols and are handled similarily to untyped AST translations (a.k.a \<open>parse AST translations\<close>) i.\,e.
      \<^emph>\<open>left-to-right\<close> and \<^emph>\<open>until fixpoint\<close> is reached. Unlike AST translations that are mostly used for very simple
      free-form translation rules, term translations are mostly used for \<^emph>\<open>complex\<close> parsing transformations that are
      programmed by hand in ML e.\,g. list and set comprehension syntaxes,
      encoding of numbers into the canonical binary representation and convenient lamda-abstractions with
      simultaneous pattern-matching (e.\,g. \<open>\<lambda> SOME (a, b). ...\<close>). Both AST and term translations can be
      context-dependant and thus can take proper care of the datatype constructor definitions
      known in the particular context.
    \<^item> \<^emph>\<open>Checking\<close> stage. This stage is just an \<^emph>\<open>ordered pipeline\<close> of functions of type
      \<^ML_type>\<open>Proof.context -> term list -> term list\<close> applied \<^emph>\<open>just once\<close> in a \<^emph>\<open>fixed pre-defined order\<close>.
      Naturally, the transformations can be very general and expressive.
      These, in particular, include the actual type inference.
      Hence they operate on lists of terms that may share the same \<^emph>\<open>flexible type variables\<close>
      (as used in the well-known Hindley-Milner type inference algorithm \<open>\<W>\<close>). Our modified ad-hoc overloading
      implementation is also applied at this stage.


  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.cterm_of\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>term\<close> : \<^ML_type>\<open>term\<close>) :\\
  \<^ML_type>\<open>cterm\<close>
  \end{tabular}\\
  Checks and certifies a term \<open>term\<close> to obtain a certified term relative to the context \<open>ctxt\<close>.
\<close>

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
    rewrite_rule \<^context> [@{thm or_def}, @{thm neg_def}] @{thm excl_mid} |>
    Thm.forall_elim \<^cterm>\<open>PROP A\<close> |>
    Thm.instantiate' [] [SOME \<^cterm>\<open>PROP A\<close>] |>
    rpair (Thm.trivial \<^cterm>\<open>PROP A\<close>) |->
    Thm.implies_elim |>
    rpair (Thm.assume \<^cterm>\<open>\<not> \<not> PROP A\<close>) ||>
    rewrite_rule \<^context> [@{thm neg_def}] ||>
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
     ((\<^binding>\<open>member\<close>, \<^typ>\<open>'a \<Rightarrow> 'a set \<Rightarrow> prop\<close>),
     Infix (Input.string "\<in>", 50, Position.no_range)) #>
   snd
\<close>

print_syntax

setup \<open>
   Sign.declare_const_global
     ((\<^binding>\<open>Collect\<close>, \<^typ>\<open>('a \<Rightarrow> prop) \<Rightarrow> 'a set\<close>), NoSyn) #>
   snd #>
   Sign.add_syntax
     Syntax.mode_default
     [("_Collect",
       Proof_Context.read_typ_syntax \<^context> "pttrn \<Rightarrow> any \<Rightarrow> 'a set",
       Mixfix (Input.string "(1{_./ _})", [], 1000, Position.no_range))] #>
   (fn thy =>
      let
        val ctxt = Proof_Context.init_global thy
      in
        Sign.add_trrules
          [Syntax.map_trrule
            (Syntax_Phases.parse_ast_pattern ctxt o pair "logic")
            (Syntax.Parse_Print_Rule ("{x. P}", "CONST Collect (\<lambda>x. P)"))]
          thy
      end)
\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>elem\<close>, \<^term>\<open>\<And>S x. x \<in> Collect S \<equiv> S x\<close>) #>>
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
   Thm.add_axiom_global (\<^binding>\<open>set\<close>, \<^term>\<open>\<And>S x. {x. x \<in> S} \<equiv> S\<close>) #>>
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
    rewrite_rule \<^context> [Thm.assume \<^cterm>\<open>A :: 'a set \<equiv> B\<close>] |>
    Thm.implies_intr \<^cterm>\<open>x \<in> A\<close> |>
    rpair (Thm.assume \<^cterm>\<open>x \<in> B\<close>) ||>
    rewrite_rule \<^context> [Thm.assume \<^cterm>\<open>A :: 'a set \<equiv> B\<close> |> Thm.symmetric] ||>
    Thm.implies_intr \<^cterm>\<open>x \<in> B\<close> |->
    Thm.equal_intr |>
    Thm.forall_intr \<^cterm>\<open>x\<close> |>
    Thm.implies_intr \<^cterm>\<open>A :: 'a set \<equiv> B\<close> |>
    rpair @{thm set} ||>
    Thm.instantiate' [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>A :: 'a set\<close>] ||>
    Thm.symmetric ||>
    pair (Thm.assume \<^cterm>\<open>\<And> x. x \<in> A \<equiv> x \<in> B\<close>) ||>
    apfst (Thm.forall_elim \<^cterm>\<open>x\<close> #> Drule.generalize ([], ["x"]) #> single) ||>
    uncurry (rewrite_rule \<^context>) ||>
    pair @{thm "set"} ||>
    apfst (Thm.instantiate' [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>B :: 'a set\<close>] #> single) ||>
    uncurry (rewrite_rule \<^context>) ||>
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

(*<*)
end
(*>*)