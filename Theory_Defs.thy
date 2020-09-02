(*<*)
theory Theory_Defs
  imports Pure
begin
(*>*)

section \<open>Inner syntax, type and constant declarations, axiomatization\<close>

subsection \<open>Isabelle/ML interfaces\<close>

text \<open>
  \marginsymbol
  \<^ML_text>\<open>eqtype\<close> \<^ML_type>\<open>Position.T\<close>\\
  An abstract type for representing \<^emph>\<open>positions\<close> in an arbitrary user input, either located in a file or in an
  interactive input field. Contains the start line number as well as the start (\<^emph>\<open>inclusive\<close>) and end (\<^emph>\<open>exclusive\<close>)
  offsets of the input text range (from the \<^emph>\<open>start of the input source\<close>, such as a file).
  The offsets are counted in \<^emph>\<open>Isabelle symbols\<close> (e.\,g. \<open>a\<close>, \<open>\<Longrightarrow>\<close>, \<open>\<longlonglongrightarrow>\<close>, \<open>\<^sub>\<close>\<^footnote>\<open>The control symbol denoting the
  subscript, not properly renderable in \LaTeX.\<close>, \<open>\<^context>\<close>\<^footnote>\<open>Yes, \<open>\<^context>\<close> and other
  \<^emph>\<open>control symbols\<close> of the form \<^verbatim>\<open>\<^something>\<close> are considered \<^emph>\<open>single\<close> Isabelle symbols.\<close>
  the opening/closing cartouche itself etc.) starting from \<open>1\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>Position.range\<close> = \<^ML_type>\<open>Position.T * Position.T\<close>\\
  A type alternatively representing position as a span between the \<^emph>\<open>starts\<close> of two positions
  \<^emph>\<open>located in the same source\<close> (e.\,g. a file), \<^emph>\<open>excluding\<close> the start of the second position.
  The difference from \<^ML_type>\<open>Position.T\<close> here is \<^emph>\<open>purely pragmatic\<close>
  with the function \<^ML>\<open>Position.range_position\<close> being able to convert the range into a position. However, the
  interfaces are designed under an assumption that \<^ML_type>\<open>Position.T\<close> is used to designate a position of a
  \<^emph>\<open>single entity\<close>, such as a keyword or a separator that may range multiple Isabelle symbols (e.\,g. \<open>=simp\<Rightarrow>\<close> or \<open>\<^sup>*\<close>
  comprised from \<open>\<^sup>\<close> and \<open>*\<close>), while \<^ML_type>\<open>Position.range\<close> denotes a fragment of user input consisting from
  multiple entities (such as tokens).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Position.none\<close> : \<^ML_type>\<open>Position.T\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Position.no_range\<close> : \<^ML_type>\<open>Position.range\<close>\\
  Dummy defaults encoding the absence of any position information.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Position.here\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>p\<close> : \<^ML_type>\<open>Position.T\<close>) :\\
  \<^ML_type>\<open>string\<close>
  \end{tabular}\\
  An auxiliary function converting position to simple readable user output, mostly for debugging.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<open>\<^here>\<close> : \<^ML_type>\<open>Position.T\<close>\\
  A convenience quotation returning the position corresponding to the symbol \<open>\<^here>\<close> itself.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>Input.source\<close>\\
  An abstract type for representing generic user input with position information. This type is widely used within
  Isabelle/ML sources to represent strings obtained by user interaction within PIDE framework. This representation
  provides positions for cross-reference and highly precise syntactic and semantic highlighting.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Input.text_of\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>Input.source\<close>) :\\
  \<^ML_type>\<open>Symbol_Pos.text\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Input.pos_of\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>Input.source\<close>) :\\
  \<^ML_type>\<open>Position.T\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Input.range_of\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>Input.source\<close>) :\\
  \<^ML_type>\<open>Position.range\<close>
  \end{tabular}\\
  Getters that extract the data from the input source. \<^ML>\<open>Input.text_of\<close> returns the actual input string
  (\<^ML_type>\<open>Symbol_Pos.text\<close> = \<^ML_type>\<open>string\<close>), \<^ML>\<open>Input.pos_of\<close> returns the starting position of the input (the
  position of the first distinguishable entity/token e.\,g. the first keyword), and
  \<^ML>\<open>Input.range_of\<close> returns the range occupied by the input string in the source.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Input.string\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>string\<close>) :\\
  \<^ML_type>\<open>Input.source\<close>
  \end{tabular}\\
  Constructs user input with \<^emph>\<open>no\<close> position information (position equal to \<^ML>\<open>Position.no_range\<close>).
\<close>
text \<open>
  \<^bigskip>

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
    Haskell's Parsec for grasping the general idea). We only mention here that Isabelle/ML's parser combinators operate
    on \<^emph>\<open>pairs\<close> with the \<^emph>\<open>second\<close> component representing the abstract stream (actually, a list) of tokens with or
    without the corresponding context. \<^emph>\<open>Context-dependant\<close> parsers operate on a pair of a context and a token stream,
    the stream being the \<^emph>\<open>second\<close> component. Hence the types\\
    \<^ML_text>\<open>type 'a parser = T list -> 'a * T list\<close>\\
    and\\
    \<^ML_text>\<open>type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list)\<close>.\\
  \<^item> The \<^emph>\<open>inner syntax\<close>, however, is defined by somewhat more Isabelle/specific and less well-known means. The inner
    syntax parsing pipeline has 5 (\<^bold>\<open>!\<close>) separate stages. Let's briefly describe them:
    \<^item> \<^emph>\<open>Lexing\<close> stage. At this stage the initial string representing the inner Isabelle logic term and already
      \<^emph>\<open>delimited\<close> by the outer theory syntax is separated into a list of \<^emph>\<open>tokens\<close>. The lexer is mostly
      pre-defined and can \<^emph>\<open>only\<close> be extended \<^emph>\<open>implicitly\<close> by adding so-called \<^emph>\<open>separators\<close> of the \<^emph>\<open>mixfix\<close>
      parsing and printing annotations as well as \<^emph>\<open>constant\<close> names. Those separators are just the tokens corresponding
      to would-be \<^emph>\<open>terminal\<close> symbols of an extensible context-free grammar. There are several pre-defined terminals,
      most importantly, the \<^emph>\<open>identifier\<close> terminal that corresponds to constants and other logical symbols with
      a fixed interpretation and the \<^emph>\<open>variable\<close> terminal,
      corresponding to uninterpreted symbols. In general, the means to
      extend the inner lexer available to the Isablle/ML user/expert are defining a new constant name and
      (implicitly) defining a new mixfix separator.
    \<^item> \<^emph>\<open>Parsing\<close> stage. At this stage the readily separated list of tokens (Isabelle inner syntax parser is generally
      \<^emph>\<open>not\<close> lazy, so it \<^emph>\<open>is\<close> possible to handle the entire inner logical term or even several closely related terms
      at once) is transformed into the \<^emph>\<open>untyped AST\<close> defined in \<^ML_structure>\<open>Ast\<close> (\<^file>\<open>~~/src/Pure/Syntax/ast.ML\<close>)
      as follows:\\
      \<^ML_text>\<open>datatype ast =
  Constant of string |
  Variable of string |
  Appl of ast list\<close>\\
      This is a very simple initial AST that, however, already distinguishes \<^emph>\<open>constants\<close> and \<^emph>\<open>variables\<close>. Meanwhile,
      the type annotations and binders (particularly, the lambda abstractions) are
      \<^emph>\<open>not yet separated from terms\<close> and are expressed using special constants \<open>_constrain\<close>, \<open>_lambda\<close>, \<open>_abs\<close>,
      \<open>_sort_constraint\<close> etc.

      The only externally available way to extend the parser is by defining a mixfix annotation
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
      the Isabelle reference manual (Section 8.2.1).
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
      translation rule is not applicable anymore. Syntactic constant names usually start with either an underscore
      or a special control prefix such as \<open>\<^const>\<close> or \<open>\<^typ>\<close>. Some of the syntactic constants are not handled at this
      stage and survive AST translation
      up to the next stage (see below), since the general approach to translation there (the application
      of translations until fixpoint) is similar.
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
      (as used in the well-known Hindley-Milner type inference algorithm \<open>\<W>\<close>). Our (PLRDF's)
      modified ad-hoc overloading implementation is also applied at this stage.


  Given the general description given above, we invite the user to refer to the Isabelle manual, sections 8.2.1--8.2.3
  to identify the meaning of the \<^ML>\<open>Mixfix\<close>, \<^ML>\<open>Infix\<close>, \<^ML>\<open>Infixl\<close>, \<^ML>\<open>Infixr\<close> and \<^ML>\<open>Binder\<close> constructors. We only
  mention that the position specified in these constructors provides the location ascribed to
  corresponding extensions of the inner syntax. The last constructor, \<^ML>\<open>Structure\<close>, is slightly deprecated and
  was used in older historical crude implementation of Isabelle locales by purely syntactic means. However, it is
  still supported and, in principle,
  can be used for implicit insertion of context-dependent fixed variables into terms at the parsing
  stage.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>Syntax.mode\<close> = \<^ML_type>\<open>string * bool\<close>\\
  A type synonym used to denote Isabelle's parsing/prining \<^emph>\<open>modes\<close>. The mechanism of modes allows rather simple support
  of different output targets, some of which may or may not support Unicode, rendering of special Isabelle symbols etc.
  A mode is just a pair of a string and a boolean flag. The string identifies a \<^emph>\<open>printing\<close> mode, such as \<^ML>\<open>""\<close> (the
  default mode), \<^ML>\<open>"ASCII"\<close> (don't use Unicode) or \<^ML>\<open>"internal"\<close> (a notation that is only used locally within a
  context of just one atomic specification e.\,g. a function definition) and \<^ML>\<open>"input"\<close> (denotes user input and
  should be never used for printing from Isabelle itself). The flag specifies whether the notation should also be
  supported (recognized/parsed) in the user input. The notion of a \<^emph>\<open>syntax mode\<close> is used not only during the
  parsing/pretty-printing per se, but sometimes also during folding/unfolding of certain constants at the
  checking/typing stage (which may also be considered part of the parsing pipeline). In practice this simply means that
  the grammar rules used for pretty-printing are stored on per-mode basis and some of the transformations may
  work differently depending on the current mode. It should be noted here that \<^emph>\<open>even debug output\<close> is Isabelle
  normally requires the efforts of the entire Isabelle printing pipeline. Hence the current printing mode is \<^emph>\<open>not\<close> part
  of a normal Isabelle context, but is kept in a separate unsynchronized (thread-unsafe) global variable
  \<^ML>\<open>print_mode\<close> that can be modified arbitrarily at any moment. The current syntax used for pretty-printing is
  combined from all the modes enabled by listing in the \<^ML>\<open>print_mode\<close> variable (of type \<^ML_type>\<open>string list\<close>).

  Also, this syntax mode is \<^emph>\<open>not the only\<close> parameter that controls the behavior of Isabelle's printing/parsing
  pipeline. In particular, there are also separate modes defined in modules \<^ML_structure>\<open>Proof_Context\<close> and
  \<^ML_structure>\<open>Type\<close> that \<^emph>\<open>are part of the context\<close> and control the behavior of the type inference as well as
  type and term certification. They, however, don't change the pipeline fundamentally and just cut off certain stages
  such as expansion of syntactic abbreviations or type propagation through unification.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Syntax.mode_default\<close> : \<^ML_type>\<open>Syntax.mode\<close> = \<^ML>\<open>("", true)\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Syntax.mode_input\<close> : \<^ML_type>\<open>Syntax.mode\<close> = \<^ML>\<open>(Print_Mode.input, true)\<close>\\
  Most commonly used syntax modes.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>datatype 'a trrule =
  Parse_Rule of 'a * 'a |
  Print_Rule of 'a * 'a |
  Parse_Print_Rule of 'a * 'a\<close>\\
  A special designated type for simple AST translations (so-called \<^emph>\<open>translation rules\<close> or \<^emph>\<open>tr-rules\<close>). Tr-rules
  are simply pairs of pattern ASTs such as \<open>_list (_args (x, xs)), Cons (x, _list xs)\<close> or
  \<open>_list x, Cons (x, Nil)\<close>. Those rules are employed during the AST translation stage and
  are  applied \<^emph>\<open>until fixpoint\<close> in a \<^emph>\<open>first-fit\<close> manner so that the rule
  that was registered first is also tried first and immediately applied, if matches. The constants in those rules are
  usually syntactic and start with an underscore, other identifiers are considered \<^emph>\<open>variables\<close>. A rule is applied
  by matching one of its sides against the AST (from left to right) and then replacing it with another side of the rule
  by instantiating its variables with the results of the matching. The rules are often specified using the
  syntax already provided by the corresponding syntactic constants e.\,g. \<open>[x, xs]\<close> for \<open>_list (_args (x, xs))\<close>
  (which corresponds to
  \<open>Ast.Appl [Ast.Constant "_list", Ast.appl [Ast.Constant "args", Ast.Variable "x", Ast.Variable "xs"]]\<close>). Actual
  non-syntactic constants can also be used in the specification and can escaped using a special construct \<open>CONST\<close>
  when needed for disambiguation with the variables (e.\,g. \<open>CONST Cons\<close>). The important detail here is that the
  same rules can in fact be applied \<^emph>\<open>both\<close> for parsing and for printing. Hence the rules fall into three groups:
  parse rules (denoted by \<^ML>\<open>Syntax.Parse_Rule\<close> and \<open>\<rightharpoonup>\<close> in outer syntax),
  print rules (\<^ML>\<open>Syntax.Print_Rule\<close>, \<open>\<leftharpoondown>\<close>) and parse/print rules (\<^ML>\<open>Syntax.Parse_Print_Rule\<close>,~\<open>\<rightleftharpoons>\<close>).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Syntax.map_trrule\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'b\<close>)\\
  (\<open>rule\<close> : \<^ML_type>\<open>'a Syntax.trrule\<close>) :\\
  \<^ML_type>\<open>'b Syntax.trrule\<close>
  \end{tabular}\\
  A convenience function for mapping each component of a tr-rule e.\,g. for parsing it from a pair of strings.
\<close>
text \<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.add_syntax\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>mode\<close> : \<^ML_type>\<open>Syntax.mode\<close>)\\
  (\<open>consts\<close> : \<^ML_type>\<open>(string * typ * mixfix) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.notation\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>add\<close> : \<^ML_type>\<open>bool\<close>)\\
  (\<open>mode\<close> : \<^ML_type>\<open>Syntax.mode\<close>)\\
  (\<open>mxs\<close> : \<^ML_type>\<open>(term * mixfix) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.add_trrules\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>trrules\<close> : \<^ML_type>\<open>Ast.ast Syntax.trrule list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.parse_ast_translation\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>transs\<close> : \<^ML_type>\<open>(string * (Proof.context -> Ast.ast list -> Ast.ast)) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.parse_translation\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>transs\<close> : \<^ML_type>\<open>(string * (Proof.context -> term list -> term)) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Syntax_Phases.term_check\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ord\<close> : \<^ML_type>\<open>int\<close>)\\
  (\<open>name\<close> : \<^ML_type>\<open>string\<close>)\\
  (\<open>check\<close> : \<^ML_type>\<open>Proof.context -> term list -> term list\<close>)\\
  (\<open>context\<close> : \<^ML_type>\<open>Context.generic\<close>) :\\
  \<^ML_type>\<open>Context.generic\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.print_ast_translation\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>transs\<close> : \<^ML_type>\<open>(string * (Proof.context -> Ast.ast list -> Ast.ast)) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.print_translation\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>transs\<close> : \<^ML_type>\<open>(string * (Proof.context -> term list -> term)) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.typed_print_translation\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>transs\<close> : \<^ML_type>\<open>(string * (Proof.context -> typ -> term list -> term)) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Syntax_Phases.term_uncheck\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ord\<close> : \<^ML_type>\<open>int\<close>)\\
  (\<open>name\<close> : \<^ML_type>\<open>string\<close>)\\
  (\<open>check\<close> : \<^ML_type>\<open>Proof.context -> term list -> term list\<close>)\\
  (\<open>context\<close> : \<^ML_type>\<open>Context.generic\<close>) :\\
  \<^ML_type>\<open>Context.generic\<close>
  \end{tabular}\\
  The main Isabelle/ML interfaces of the parsing/printing pipeline (on a global theory level). The semantics of
  the interfaces should be more or less intuitive based on the general description given above. Here
  it only worth noting the peculiar relationship between the syntax and typing in the \<^ML>\<open>Sign.add_syntax\<close> interface and
  some elaboration about the \<^ML>\<open>Sign.typed_print_translation\<close>. The mixfix annotations specified in \<^ML>\<open>Sign.add_syntax\<close>
  only define the \<^emph>\<open>priorities\<close> \<open>p\<close> of the corresponding grammar rules. However, to fully determine the rules we
  need the full non-terminals represented by pairs \<open>nonterm\<^bsup>(p)\<^esup>\<close>. The non-terminal (\<open>nonterm\<close>) itself is determined
  from the \<^emph>\<open>semi-syntactic\<close> type of the constant. This type can include both normal Isabelle types such as
  \<^typ>\<open>prop\<close>, \<open>'a set\<close>, \<open>int\<close>, \<open>'a \<times> 'b\<close> or \<open>'a + 'b\<close> (the sum type) and so-called \<^emph>\<open>syntactic types\<close> that actually
  correspond to non-terminals of the inner syntax grammar. Those include \<open>args\<close> for comma-separated lists of
  arbitrary constructs (both types and terms), \<open>logic\<close> for terms, \<open>type\<close> for types, \<open>pttrn\<close> for binding patterns
  that can be used within the binding part of the lambda (e.\,g. \<open>\<lambda> (a, b, c). \<dots>\<close> with the tuple pattern in the
  binding), \<open>any\<close> for both terms and types, among many others. A non-syntactic (``normal'') type specified in the
  type of a \<^emph>\<open>term\<close> constant will be interpreted as \<open>logic\<close> non-terminal, unless it is a type variable that
  will be interpreted as \<open>any\<close>. The special case of type variable is justified by the grammar rules of Pure, which
  do not recognize the type \<^typ>\<open>prop\<close> in all contexts (only at the top level), so if the variable turns out to
  be instantiated with that type, it has to be parsed differently. The reason for using the special \<open>PROP\<close> construct
  is the same. This enables slightly more flexibility in defining the syntax of the object logics such as HOL by
  avoiding some grammar conflicts near the boundaries of the object logic terms, namely the object-level term
  cannot span over the meta-connectives such as \<open>\<Longrightarrow>\<close>. \<^ML>\<open>Sign.add_syntax\<close> can add syntax for both normal (logic)
  as well as syntactic constants (that are to be translated later down the pipeline). \<^ML>\<open>Sign.notation\<close> is very
  similar to \<^ML>\<open>Sign.add_syntax\<close>, albeit it is adapted for adding \<^emph>\<open>or deleting\<close> (according to the
  \<open>add\<close> parameter) the syntax for already existing
  constants by automatically translating logic constants (registered in the theory context) into their syntactic
  counterparts. Internally, both \<^ML>\<open>Sign.add_syntax\<close> and \<^ML>\<open>Sign.notation\<close> use the same interfaces, so no error
  is expected if \<^ML>\<open>Sign.add_syntax\<close> is misused for adding a notation for existing constant or vise versa. Another
  notable detail is that the type in \<^ML>\<open>Sign.typed_print_translation\<close> is the type of the \<^emph>\<open>constant\<close>, not the term
  formed by its application to the arguments. Typed print translations are analogous to the usual print translations,
  only different in the fact they are applied before the end of the uncheck phase, where types in Isabelle terms
  can be replaced by dummies.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Syntax_Phases.parse_ast_pattern\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>root_ast\<close> : \<^ML_type>\<open>string * string\<close>) :\\
  \<^ML_type>\<open>Ast.ast\<close>
  \end{tabular}\\
  A convenience function to parse a string into an untyped AST. Primarily intended to be used for parsing tr-rules.
  The tr-rule is specified as a pair \<open>(root, pat)\<close>, where \<open>root\<close> is the non-terminal to start the parsing (normally,
  \<open>logic\<close>) and \<open>pat\<close> is the inner syntax to be parsed.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Proof_Context.read_typ_syntax\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>typ\<close> : \<^ML_type>\<open>string\<close>) :\\
  \<^ML_type>\<open>typ\<close>
  \end{tabular}\\
  A convenience function for reading (parsing) the \<^emph>\<open>semi-syntactic\<close> types used for specifying the type of syntactic
  constants (particularly, when invoking \<^ML>\<open>Sign.add_syntax\<close>).
\<close>
text \<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.declare_const_global\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>decl\<close> : \<^ML_type>\<open>(binding * typ) * mixfix\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>term * theory\<close>
  \end{tabular}\\
  Declares a global \<^emph>\<open>yet uninterpreted\<close> constant. The interpretation is to be \<^emph>\<open>added later\<close> by providing the
  corresponding axiomatization. Note that definitions are also axioms, notwithstanding the fact their
  consistency is ensured by the appropriate acyclicity checks as well as the reflexivity and substituativity of
  equality. The first component of the returned pair is just the term representing the constant (\<^ML_text>\<open>Const c\<close>).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Sign.add_types_global\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>decl\<close> : \<^ML_type>\<open>(binding * int * mixfix) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>term * theory\<close>
  \end{tabular}\\
  Declares new \<^emph>\<open>type constructors\<close> with the specified numbers of type arguments. Just as with constants, the types
  are initially entirely uninterpreted. Note that type constructors can also have syntax, as for instance the
  pair constructor \<open>'a \<times> 'b\<close> (actually \<open>('a, 'b) prod\<close>) or the sum type constructor \<open>+\<close> (\<open>('a, 'b) sum\<close>).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Global_Theory.add_defs\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>overloaded\<close> : \<^ML_type>\<open>bool\<close>)\\
  (\<open>defs\<close> : \<^ML_type>\<open>((binding * term) * attribute list) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>thm list * theory\<close>
  \end{tabular}\\
  Admits definitional axioms in the global theory. The definitions are checked for acyclicity (in the order they
  previously were or are currently being added to the theory) and thus are
  guaranteed to be consistent. The \<open>overloaded\<close> parameter enables ad-hoc overloading of a polymorphic constant by
  providing a definition only for a \<^emph>\<open>particular type instantiation\<close>. Both the provided definitional axioms
  (\<open>defs\<close>) and the corresponding returned theorems
  should of the form \<open>b \<equiv> t\<close>, where \<open>b\<close> is the constant (specified in the \<open>binding\<close>) and \<open>t\<close> is the
  desired RHS term. Attributes are not discussed in this section (see the section on tactical reasoning for some
  more details) and are not relevant for basic use of definitions, thus an empty list of attributes often suffices.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.no_attributes\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>) :\\
  \<^ML_type>\<open>'a * 'b list\<close> &= \<^ML_text>\<open>(x, [])\<close>
  \end{tabular}\\
  A convenient and self-explanatory shortcut for attaching no attributes to some particular argument when using
  Isabelle/ML interfaces that require them.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.simple_fact\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>) :\\
  \<^ML_type>\<open>('a * 'b list) list\<close> &= \<^ML_text>\<open>[(x, [])]\<close>
  \end{tabular}\\
  Another analogous convenient shortcut for singleton lists.

  \<^bigskip>

  \color{red}
  \marginsymbol
  \normalcolor
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.add_axiom_global\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ax\<close> : \<^ML_type>\<open>binding * term\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>(string * thm) * theory\<close>
  \end{tabular}\\
  An interface for adding arbitrary unchecked axioms. Should be used \<^emph>\<open>only in the definitions of object logics\<close> and
  not in specifications. The soundness (consistency) of the axioms should be proved at least informally, better
  by relying on some well-known results (such as the consistency of ZF or simply-typed formalization of the set
  theory). {\color{red}\<^bold>\<open>Don not use this function\<close>} in any ordinary (read just \<^emph>\<open>any\<close> code). Here it is provided only
  for educatory purposes to understand how object logics (such as HOL) are actually initially defined and bootstrapped.
  Note that the axioms of Pure are not enough to formalize common mathematics, the usual formalizations rely on
  the set theory, which is indeed sufficient for most purposes. Same approach is used in HOL, which only adds
  axioms describing the object-level connectives (\<open>=\<close> and \<open>\<longrightarrow>\<close>),
  the definite and arbitrary choice operators
  (\<open>The\<close> and \<open>Eps\<close>), the axiom of choice (\<open>P \<or> \<not> P\<close>), the mathematical induction principle (the injectivity of
  the successor function as well as the fact \<open>0 \<noteq> 1\<close>), and the description operator of the set theory (\<open>{x | P x}\<close>).
  Everything else is inferred from these axioms (modulo consistent definitional extensions).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Global_Theory.add_thm\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thms\<close> : \<^ML_type>\<open>(binding * thm) * attribute list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>thm * theory\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Global_Theory.add_thms\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thms\<close> : \<^ML_type>\<open>((binding * thm) * attribute list) list\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>thm list * theory\<close>
  \end{tabular}\\
  Registers the theorems in the provided global theory by their names.
\<close>
text \<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>rewrite_rule\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>\\
  (\<open>rules\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>)\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  One of the basic interfaces of the Isabelle \<^emph>\<open>simplifier\<close>. This function is roughly similar to applying the
  method @{method simp} to a subgoal equal to the provided theorem \<open>thm\<close> and returning the obtained
  simplified subgoal as the result. This is especially useful for \<^emph>\<open>iterative\<close> forward rewriting of theorem
  statements as in folding/unfolding of definitions, normalization (e.\,g. modulo associativity and commutativity)
  or some other equivalent transformations based on rewriting.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>apfst\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'c\<close>\\
  (\<open>x\<close> : \<^ML_type>\<open>'a * 'b\<close>) :\\
  \<^ML_type>\<open>'c * 'b\<close> &= \<^ML_text>\<open>(f (fst x), snd x)\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>apsnd\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'b -> 'c\<close>\\
  (\<open>x\<close> : \<^ML_type>\<open>'a * 'b\<close>) :\\
  \<^ML_type>\<open>'a * 'c\<close> &= \<^ML_text>\<open>(fst x, f (snd x))\<close>
  \end{tabular}\\
  Some more convenient standard combinators.
\<close>

subsection \<open>Problems\<close>

text \<open>
  \<^enum> Define global constants \<open>\<or>\<close> and \<open>\<not>\<close> formalizing the disjunction and
    negation of Pure propositions (type \<^typ>\<open>prop\<close>) with the corresponding syntax and \<^emph>\<open>definitional\<close> axiomatization.
    \<^bold>\<open>Hint\<close>: to come up with the corresponding definitions and appropriate syntax annotations, a look into the
    fundamental definitions of the HOL theory in \<^file>\<open>~~/src/HOL/HOL.thy\<close> may be helpful.
  \<^enum> Add the law of excluded middle (\<open>A \<or> \<not> A\<close>) as an axiom using the defined global constants representing
    disjunction and negation. Prove the rule of double negation (\<open>\<not>\<not>A \<equiv> A\<close>) from the law of excluded middle.
  \<^enum> Define global abstract type \<open>'a set\<close>, an abstract operation \<open>\<in>\<close> and an abstract operator \<open>{_. _}\<close> (the
    so-called \<^emph>\<open>set-builder notation\<close>, where Isabelle idiosyncratically prefers the dot over the pipe)
    with the corresponding syntax.
  \<^enum> Come up with a minimal axiomatization of the semantics for the membership and set-builder operators. These
    axioms are in fact sufficient to fully express the entire simply-typed set theory!
  \<^enum> Add the axiomatic specification of the membership and set-builder operators to the current theory.
    Prove the set equality criterion \<open>(A \<equiv> B) \<equiv> (\<And>x. x \<in> A \<equiv> x \<in> B)\<close> based on the added axiomatic specification.
  \<^enum> Add a definition of a global constant \<open>C\<close> representing the set of all constant functions of one argument.
    Prove the theorem \<open>f \<in> C \<equiv> (\<And>x y. f x \<equiv> f y)\<close>.
\<close>

subsection \<open>Solutions\<close>

subsubsection \<open>Problem 1\<close>

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
   pair (\<^binding>\<open>neg_def\<close>, \<^term>\<open>\<not> PROP A \<equiv> (PROP A \<Longrightarrow> (\<And>P. PROP P))\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_defs false #>
   snd
\<close>

subsubsection \<open>Problem 2\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>excl_mid\<close>, \<^term>\<open>\<And>P. PROP P \<or> \<not> PROP P\<close>) #>>
   apsnd (Thm.forall_elim \<^cterm>\<open>PROP P\<close> #> Drule.generalize ([], ["P"])) #>>
   apfst (K \<^binding>\<open>excl_mid\<close>) #>>
   Thm.no_attributes #->
   Global_Theory.add_thm #>
   snd
\<close>

ML \<open>
  val prove_double_negation =
    let
      val ltr =
        @{thm excl_mid} |>
        Thm.instantiate' [] [SOME \<^cterm>\<open>PROP A\<close>] |>
        rewrite_rule \<^context> [@{thm or_def}] |>
        Thm.forall_elim \<^cterm>\<open>PROP A\<close> |>
        rpair (Thm.trivial \<^cterm>\<open>PROP A\<close>) |->
        Thm.implies_elim |>
        rpair (Thm.assume \<^cterm>\<open>\<not> \<not> PROP A\<close>) ||>
        (rpair (Thm.assume \<^cterm>\<open>\<not> PROP A\<close>) #>
         apply2 (rewrite_rule \<^context> [@{thm neg_def}]) #->
         Thm.implies_elim #>
         Thm.forall_elim \<^cterm>\<open>PROP A\<close> #>
         Thm.implies_intr \<^cterm>\<open>\<not> PROP A\<close>) |->
        Thm.implies_elim |>
        Thm.implies_intr \<^cterm>\<open>\<not> \<not> PROP A\<close>
       val rtl =
        Thm.assume \<^cterm>\<open>\<not> PROP A\<close> |>
        rewrite_rule \<^context> [@{thm neg_def}] |>
        rpair (Thm.assume \<^cterm>\<open>PROP A\<close>) |->
        Thm.implies_elim |>
        Thm.implies_intr \<^cterm>\<open>\<not> PROP A\<close> |>
        Thm.implies_intr \<^cterm>\<open>PROP A\<close> |>
        rewrite_rule \<^context> [@{thm neg_def} |> Thm.symmetric]
    in
      Thm.equal_intr ltr rtl |>
      Drule.generalize ([], ["A"]) |>
      pair \<^binding>\<open>double_negation\<close> |>
      Thm.no_attributes |>
      Global_Theory.add_thm #>
      snd
    end
\<close>

setup \<open>prove_double_negation\<close>

thm double_negation

subsubsection \<open>Problem 3\<close>

setup \<open>Sign.add_types_global [(\<^binding>\<open>set\<close>, 1, NoSyn)]\<close>

setup \<open>
   Sign.declare_const_global
     ((\<^binding>\<open>member\<close>, \<^typ>\<open>'a \<Rightarrow> 'a set \<Rightarrow> prop\<close>),
     Infix (Input.string "\<in>", 50, Position.no_range)) #>
   snd
\<close>

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

subsubsection \<open>Problem 5 (directly contains solution of problem 4)\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>elem\<close>, \<^term>\<open>\<And>S x. x \<in> Collect S \<equiv> S x\<close>) #>>
   apsnd
     (Thm.forall_elim \<^cterm>\<open>S :: _ \<Rightarrow> prop\<close> #>
      Thm.forall_elim \<^cterm>\<open>x\<close> #>
      Drule.generalize (["'a"], ["S", "x"])) #>>
   apfst (K \<^binding>\<open>elem\<close>) #>>
   Thm.no_attributes #->
   Global_Theory.add_thm #>
   snd
\<close>

setup \<open>
   Thm.add_axiom_global (\<^binding>\<open>set\<close>, \<^term>\<open>\<And>S x. {x. x \<in> S} \<equiv> S\<close>) #>>
   apsnd
     (Thm.forall_elim \<^cterm>\<open>S :: _ set\<close> #>
      Thm.forall_elim \<^cterm>\<open>x :: 'b\<close> #>
      Drule.generalize (["'a"], ["S", "x"])) #>>
   apfst (K \<^binding>\<open>set\<close>) #>>
   Thm.no_attributes #->
   Global_Theory.add_thm #>
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
    pair @{thm set} ||>
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

subsubsection \<open>Problem 6\<close>

setup \<open>Sign.declare_const_global ((\<^binding>\<open>C\<close>, \<^typ>\<open>('a \<Rightarrow> 'b) set\<close>), NoSyn) #> snd\<close>

setup \<open>
   pair
    (\<^binding>\<open>C_def\<close>,
     \<^term>\<open>C \<equiv> {f. \<And> x y. f x \<equiv> f y}\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_defs false #>
   snd
\<close>

ML \<open>
  val prove_C_iff =
    @{thm set_eq_iff} |>
    Thm.instantiate' [SOME \<^ctyp>\<open>'a \<Rightarrow> 'b\<close>] [SOME \<^cterm>\<open>C\<close>, SOME \<^cterm>\<open>{f. \<And> x y. f x \<equiv> f y}\<close>] |>
    rpair (@{thm C_def} |> Thm.instantiate' [SOME \<^ctyp>\<open>'a\<close>, SOME \<^ctyp>\<open>'b\<close>] []) |->
    Thm.equal_elim |>
    Thm.forall_elim \<^cterm>\<open>f :: 'a \<Rightarrow> 'b\<close> |>
    rewrite_rule \<^context> [@{thm elem}] |>
    Drule.generalize (["'a", "'b"], ["f"]) |>
    pair \<^binding>\<open>C_iff\<close> |>
    Thm.no_attributes |>
    Global_Theory.add_thm #>
    snd
\<close>

setup \<open>prove_C_iff\<close>

thm C_iff

(*<*)
end
(*>*)