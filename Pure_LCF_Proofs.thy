(*<*)
theory Pure_LCF_Proofs
  imports Pure
begin
(*>*)

section \<open>Primitive LCF-style proofs in Isabelle/Pure\<close>

subsection \<open>Isabelle/ML interfaces\<close>

text \<open>
  \marginsymbol
  \<^ML_text>\<open>datatype term =
  Const of string * typ |
  Free of string * typ |
  Var of indexname * typ |
  Bound of int |
  Abs of string * typ * term |
  $ of term * term\<close>\\
  The main type representing Isabelle terms. Note that there are three distinct kind of variables:
  \<^item> \<open>free\<close> variables (represented by the \<^ML>\<open>Free\<close> constructor and displayed in blue)
    are those well-known \<open>arbitrary, but fixed\<close>
    variables that are normally used during mathematical
    proofs and are later \<open>generalized\<close> (e.\,g. as in the usual phrase `since \<open>\<epsilon>\<close> was chosen arbitrarily') to obtain a
    quantified proposition (e.\,g. \mbox{\<open>\<And> \<epsilon>. P \<epsilon>\<close>}). In Isabelle, however, the top-level universal quantification is
    \<open>implicit\<close> and is expressed using \<open>schematic\<close> variables.
  \<^item> \<open>schematic\<close> variables (represented by the \<^ML>\<open>Var\<close> constructor and displayed in blue with a question mark e.\,g.
    \<open>?x\<close>) are top-level universally quantified variables. They can be instantiated directly using
    designated Isabelle/ML interfaces e.\,g. \<^ML>\<open>Thm.instantiate'\<close>. This is unlike \<open>bound\<close> variables e.\,g.
    \<open>\<And>x. \<dots> x \<dots>\<close>, where a special theorem (\<open>rule\<close>) has to be employed to instantiate them
    (e.\,g. \<open>meta_spec\<close>: \mbox{@{thm meta_spec}}).
  \<^item> \<open>bound\<close> variables (represented by the \<^ML>\<open>Bound\<close> constructor and displayed in green) are variables that exist
    within a clearly delimited \<open>scope\<close> represented by the \<^ML>\<open>Abs\<close> constructor that corresponds to
    lambda-abstraction. Occurrences of bound variables are designated not by their names, but by
    \<open>de Bruijn indices\<close> counted from \<open>0\<close> in the \<open>inside-out\<close> direction (e.\,g. the body of \<open>\<lambda> x y. x y\<close> is
    \mbox{\<open>Bound 1 $ Bound 0\<close>}).


  Relative to a \<open>context\<close>, free variables are also categorized into \<open>locally fixed\<close>
  (fixed at the top level of the proof, displayed in blue) and \<open>skolem\<close> variables
  (fixed at some inner level inside the proof, displayed in orange). Globally fixed variables are called \<open>constants\<close>.
  They have certain semantics conveyed through the axioms of the logic and its consistent extensions such as
  various kinds of definitions (function, datatype, record etc.). The \<open>$\<close> is an infix constructor and corresponds to
  \<open>application\<close> e.\,g. in \<open>f x\<close>. Note that the logic is higher-order and thus the applications are currified, so
  \<open>f x y\<close> becomes \<open>f $ x $ y\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>cterm\<close>\\
  The type of \<open>certified\<close> terms relative to a certain \<open>context\<close>. Those terms are guaranteed to be
  well-formed (e.\,g. all de-Bruijn indices occur within the corresponding scopes) and, in particular,
  correctly typed. There are also corresponding types representing Isabelle/Pure \<open>types\<close> (\<^ML_type>\<open>typ\<close>) and
  \<open>certified types\<close> (\<^ML_type>\<open>ctyp\<close>).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>datatype typ =
  Type  of string * typ list |
  TFree of string * sort |
  TVar  of indexname * sort\<close>\\
  Note that there are also \<open>free\<close> and \<open>schematic\<close> \<open>type variables\<close>. Their use is analogous to that of term variables
  described above.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.cterm_of\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>term\<close> : \<^ML_type>\<open>term\<close>) :\\
  \<^ML_type>\<open>cterm\<close>
  \end{tabular}\\
  Checks and certifies a term \<open>term\<close> to obtain a certified term relative to the context \<open>ctxt\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<open>\<^context>\<close> : \<^ML_type>\<open>Proof.context\<close>\\
  Obtains a proof context corresponding to the current theory context at the beginning of the current @{command ML} or
  @{command ML_file} block. The context contains all declarations available at the beginning of the block in the outer
  theory. Very useful with many Isabelle/ML interfaces e.\,g.
  \<open>Thm.cterm_of \<^context> (Var (("x", 0), Type ("prop", [])))\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<open>\<^term>\<open>term\<close>\<close> : \<^ML_type>\<open>term\<close>\\
  \<^ML_text>\<open>val\<close> \<open>\<^typ>\<open>'typ\<close>\<close> : \<^ML_type>\<open>typ\<close>\\
  Convenient quotations for parsing of terms and types in the current context (the one returned by \<open>\<^context>\<close>).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<open>\<^cterm>\<open>term\<close>\<close> : \<^ML_type>\<open>cterm\<close>\\
  \<^ML_text>\<open>val\<close> \<open>\<^ctyp>\<open>'typ\<close>\<close> : \<^ML_type>\<open>ctyp\<close>\\
  Convenient quotations for parsing \<^emph>\<open>and certifying\<close> the terms and types in the current context.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.trivial\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>term\<close> : \<^ML_type>\<open>cterm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  An LCF implementation of the \<^emph>\<open>trivial implication\<close> inference rule a.k.a the \<open>assumption rule\<close> \<open>A \<Longrightarrow> A\<close>.
  The term \<open>A\<close> is passed as the parameter \<open>term\<close>.

  LCF methodology offers an approach for efficient, but highly reliable proof
  construction, where theorems can only be constructed by using a small number of pre-defined interfaces forming
  so-called \<open>proof kernel\<close> or \<open>logical core\<close>, whose implementation is trusted. Apart from the axioms of the logic
  (Pure and an object logic such as HOL) and the consistency of definitional extensions (definition dependency graph
  should be acyclic), the correctness of all
  proofs in the target object logic (such as HOL) is ensured by the correctness of that small proof kernel. The
  Isabelle's proof kernel is completely contained within just a single ML module \<^ML_structure>\<open>Thm\<close> (implemented
  in file \<^file>\<open>~~/src/Pure/thm.ML\<close>).

  The theorems are not simply certified and verified propositions, they also
  contain a certain auxiliary data that enables their efficient manipulation. In particular, the theorem carries
  a number of \<open>hypotheses\<close> forming theorem's own local proof context. This context is necessary for efficient
  composition of theorems. Consider the following situation:
  Let's assume we have two theorems: \<open>A \<Longrightarrow> B \<Longrightarrow> C\<close> and \<open>D \<Longrightarrow> B\<close>. From them we can normally
  derive a third theorem \<open>A \<Longrightarrow> D \<Longrightarrow> C\<close>. However, if we restrict ourselves to only simple purely syntactic inference
  rules, this idea becomes quite
  hard to express in general since the number of the the additional hypotheses (e.\,g. \<open>A\<close> and \<open>D\<close>) is generally
  unbounded. How we'd write the corresponding inference rule? \<open>(A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> (D \<Longrightarrow> B) \<Longrightarrow> (A \<Longrightarrow> D \<Longrightarrow> C)\<close>?
  \<open>(A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> (D \<Longrightarrow> E \<Longrightarrow> B) \<Longrightarrow> (A \<Longrightarrow> D \<Longrightarrow> E \<Longrightarrow> C)\<close>? This representation is always not general enough.
  For that reason we switch to a slightly different representation: \<open>A \<turnstile> B \<Longrightarrow> C\<close> and \<open>D \<turnstile> B\<close>. Now we
  only need just \<^emph>\<open>one\<close> inference rule of the form \<open>(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B\<close> to obtain the desired theorem \<open>A, D \<turnstile> C\<close>.
  The part to the left of the turnstile (\<open>\<turnstile>\<close>) is comprised of the theorem's hypotheses. The hypotheses are to be
  \<open>introduced\<close> into the theorem as assumptions in arbitrary order to obtain any of the final theorems such as
  \<open>A \<Longrightarrow> D \<Longrightarrow> C\<close> or \<open>D \<Longrightarrow> A \<Longrightarrow> C\<close>. When combining any two theorems using an inference rule, their hypotheses are
  merged (as sets, so that the there are always no repetitions).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.assume\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>term\<close> : \<^ML_type>\<open>cterm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  An LCF implementation of an \<open>assumption\<close>, a lifted form of the \<^emph>\<open>assumption rule\<close> i.\,e. \<open>A \<turnstile> A\<close>,
  where the assumption \<open>A\<close> (\<open>term\<close>) is lifted into a hypothesis.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.implies_elim\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thmAB\<close> : \<^ML_type>\<open>thm\<close>)\\
  (\<open>thmA\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  An LCF implementation of the \<open>implication elimination\<close> rule \<open>(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B\<close>: given the theorems of the
  form \<open>A \<Longrightarrow> B\<close> (\<open>thmAB\<close>) and \<open>A\<close> (\<open>thmA\<close>), returns the theorem representing the proposition \<open>B\<close>.
  To lift an assumption,
  say \<open>A\<close>, into a hypothesis, we thus can use a ``code pattern'' \<open>Thm.implies_elim thmAB (Thm.assume \<^cterm>\<open>A\<close>)\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.implies_intr\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>term\<close> : \<^ML_type>\<open>cterm\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  An LCF implementation of the \<open>implication introductoin\<close> rule, moving a hypothesis \<open>term\<close> into an assumption. The
  assumption is added \<^emph>\<open>on the left\<close>. The rule works even if the provided \<open>term\<close> is \<^emph>\<open>not\<close> a hypothesis, which is
  also correct (a spurious irrelevant assumption just weakens the theorem). A typical usage example:
\<close>
ML \<open>
  Thm.implies_elim (Thm.assume \<^cprop>\<open>PROP A \<Longrightarrow> PROP B\<close>) (Thm.assume \<^cprop>\<open>PROP A\<close>) |>
  Thm.implies_intr \<^cterm>\<open>PROP A\<close> |>
  Thm.implies_intr \<^cterm>\<open>PROP A \<Longrightarrow> PROP B\<close>
\<close>
text \<open>
  This produces a theorem \<open>(PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP A \<Longrightarrow> PROP B\<close>. Note the \<open>PROP A\<close> notation for Pure
  propositions of type \<^typ>\<open>prop\<close>.
  This is needed for propositions of the meta-logic, in contrast to the (usually) more common propositions of
  the object logics (such as HOL) that don't need the \<open>PROP\<close> prefix and have type \<open>bool\<close>. Since in this section we
  only discuss the meta logic Pure, we'll always need these \<open>PROP\<close> prefixes.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 1 |> |-> |>> ||>\<close>\\
  \<^ML_text>\<open>infix 1 #> #-> #>> ##>\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>|>\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>)\\
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'b\<close>) :\\
  \<^ML_type>\<open>'b\<close> &= \<^ML_text>\<open>f x\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>|->\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a * 'b\<close>)\\
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'b -> 'c\<close>) :\\
  \<^ML_type>\<open>'c\<close> &= \<^ML_text>\<open>f (fst x) (snd x)\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>|>>\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a * 'b\<close>)\\
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'c\<close>) :\\
  \<^ML_type>\<open>'c * 'b\<close> &= \<^ML_text>\<open>(f (fst x), snd x)\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>||>\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a * 'b\<close>)\\
  (\<open>f\<close> : \<^ML_type>\<open>'b -> 'c\<close>) :\\
  \<^ML_type>\<open>'a * 'c\<close> &= \<^ML_text>\<open>(fst x, f (snd x))\<close>
  \end{tabular}\\
  \\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>#>\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'x -> 'a\<close>)\\
  (\<open>g\<close> : \<^ML_type>\<open>'a -> 'b\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'x\<close>) :\\
  \<^ML_type>\<open>'b\<close> &= \<^ML_text>\<open>x |> f |> g\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>#->\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'x -> 'a * 'b\<close>)\\
  (\<open>g\<close> : \<^ML_type>\<open>'a -> 'b -> 'c\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'x\<close>) :\\
  \<^ML_type>\<open>'c\<close> &= \<^ML_text>\<open>x |> f |-> g\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>#>>\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'x -> 'a * 'b\<close>)\\
  (\<open>g\<close> : \<^ML_type>\<open>'a -> 'c\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'x\<close>) :\\
  \<^ML_type>\<open>'c * 'b\<close> &= \<^ML_text>\<open>x |> f |>> g\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>##>\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'x -> 'a * 'b\<close>)\\
  (\<open>g\<close> : \<^ML_type>\<open>'b -> 'c\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'x\<close>) :\\
  \<^ML_type>\<open>'a * 'c\<close> &= \<^ML_text>\<open>x |> f ||> g\<close>
  \end{tabular}\\
  Most important Isabelle/ML combinators. Useful for building long chains of consecutive transformations, possibly
  involving some shared state. The shared state is normally carried through the \<^emph>\<open>second\<close> component of a pair. Also,
  there's a convention that the shared state is passed as the \<^emph>\<open>first\<close> parameter of the function if it is only \<^emph>\<open>read\<close>
  by the function (and thus left unmodified), and as the \<^emph>\<open>last\<close> parameter if it is also \<^emph>\<open>written\<close>
  (and the new state is then
  returned as the second component of the returned pair). More combinators can be found in modules
  \<^ML_structure>\<open>Basics\<close> (\<^file>\<open>~~/src/Pure/General/basics.ML\<close>) and
  \<^ML_structure>\<open>Library\<close> (\<^file>\<open>~~/src/Pure/library.ML\<close>).

  In particular, there's a combinator \<^ML_text>\<open>||>>\<close> that chains a
  shared state through two consecutive function applications, while forming a pair of resulting values e.\,g.\\
  \<^ML_text>\<open>ctxt |> register f ||>> register x |-> handle_app\<close>,\\ which is equivalent to\\
  \<^ML_text>\<open>let
  val (f, ctxt') = register f ctxt
  val (x, ctxt'') = register x ctxt'
in
  handle_app (f, x) ctxt''
end\<close>.\\
  This is a nice example of those conventions at work. However, Isabelle/ML does not have a full-fledged support for
  monads or algebraic effects and thus this ``poor man's state monad'' remains one of the most important programming
  patterns in Isabelle/ML.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>pair\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>a\<close> : \<^ML_type>\<open>'a\<close>)\\
  (\<open>b\<close> : \<^ML_type>\<open>'b\<close>) :\\
  \<^ML_type>\<open>'a * 'b\<close> &= \<^ML_text>\<open>(a, b)\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>rpair\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>a\<close> : \<^ML_type>\<open>'a\<close>)\\
  (\<open>b\<close> : \<^ML_type>\<open>'b\<close>) :\\
  \<^ML_type>\<open>'b * 'a\<close> &= \<^ML_text>\<open>(b, a)\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>apply2\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'b\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'a * 'a\<close>) :\\
  \<^ML_type>\<open>'b * 'b\<close> &= \<^ML_text>\<open>(f (fst x), f (snd x))\<close>
  \end{tabular}\\
  Some more of the useful combinators. In particular, \<open>pair\<close> and \<open>rpair\<close> enable supplying an additional state or parameter at some
  intermediate point in a sequence of (possibly stateful) transformations. E.\,g. we can rewrite an expression\\
  \<open>Thm.implies_elim (Thm.assume \<^cprop>\<open>PROP A \<Longrightarrow> PROP B\<close>) (Thm.assume \<^cprop>\<open>PROP A\<close>)\<close>\\
  in a more sequential fashion as
\<close>
ML \<open>
\<^cprop>\<open>PROP A \<Longrightarrow> PROP B\<close> |>
Thm.assume |>
rpair \<^cprop>\<open>PROP A\<close> ||>
Thm.assume |->
Thm.implies_elim
\<close>
text \<open>

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>mk_implies\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>terms\<close> : \<^ML_type>\<open>cterm * cterm\<close>) :\\
  \<^ML_type>\<open>cterm\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.all\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>v\<close> : \<^ML_type>\<open>cterm\<close>)\\
  (\<open>t\<close> : \<^ML_type>\<open>cterm\<close>) :\\
  \<^ML_type>\<open>cterm\<close>
  \end{tabular}\\
  Two convenience shortcuts for constructing certified terms directly from other certified terms (otherwise we'd have
  to use \<^ML>\<open>Thm.cterm_of\<close> and \<^ML>\<open>Thm.term_of\<close> to certify/uncertify terms back and forth).  \<^ML>\<open>mk_implies\<close> builds a
  meta-implication (\<open>\<Longrightarrow>\<close>), while \<^ML>\<open>Thm.all\<close> builds a meta-quantifier (\<open>\<And>\<close>) by abstracting over the specified term
  \<open>v\<close> occurring inside the term \<open>t\<close>. The newly introduced lambda-body \<open>t\<close> should \<^emph>\<open>not\<close> contain loose bound variables
  (\<^ML_text>\<open>Bound i\<close>, where \<open>i\<close> is too big, i.\,e. bigger or equal to the number of enclosing lambdas).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.forall_intr\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>v\<close> : \<^ML_type>\<open>cterm\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  An LCF implementation of (meta-) \<^emph>\<open>quantifier introduction\<close> rule \<open>P v \<Longrightarrow> \<And> v. P v\<close>, where \<open>v\<close>
  is a free or schematic \<^emph>\<open>variable\<close>. The variable \<^emph>\<open>must not\<close> occur in the hypotheses of the theorem. Otherwise,
  application of this function
  corresponds to the moment when we explicitly quantify over those ``arbitrary, but fixed'' variables that were
  used during the proof.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Drule.generalize\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>vars\<close> : \<^ML_type>\<open>string list * string list\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  A \<open>generalization rule\<close> \<open>P a \<Longrightarrow> P ?a\<close>. Similar to the quantifier introduction rule, but simultaneously
  supports \<^emph>\<open>many type and term\<close> variables and introduces implicit schematic quantification rather than the
  universal quantifier. The pair \<open>vars\<close> specifies lists of \<^emph>\<open>type\<close> and \<^emph>\<open>then term\<close> variables that must occur \<^emph>\<open>free\<close>
  in the theorem, but \<^emph>\<open>not in its hypotheses\<close>. Not that there is \<^emph>\<open>no universal quantification for types\<close> in Isabelle.
  The schematic quantification is \<^emph>\<open>the only\<close> mean of type abstraction.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.instantiate'\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>typs\<close> : \<^ML_type>\<open>ctyp option list\<close>)\\
  (\<open>terms\<close> : \<^ML_type>\<open>cterm option list\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  The ``reverse'' rule for \<^emph>\<open>instantiation\<close> of schematic type and term variables. Instantiates type and term variables
  in the \<^emph>\<open>left-to-right\<close> order of their appearance in the statement of the theorem (actually, in its internal
  representation). When provided with \<open>NONE\<close>, skips the instantiation of the variable (leaving it as a schematic).
  This function \<^emph>\<open>only\<close> performs the
  instantiation and \<^emph>\<open>does not\<close> beta, eta or alpha-normalize the theorem i.\,e. \<open>(\<And> A. ?A A) \<Longrightarrow> B\<close> can be instantiated
  with \<open>A\<close> to obtain \<open>(\<And> A. A A) \<Longrightarrow> B\<close>, which is correctly represented internally (due to de Bruijn encoding),
  but is not properly readable. The default Isabelle/ML printer for type \<^ML_type>\<open>thm\<close>, however, \<^emph>\<open>does\<close>
  perform alpha, beta and eta-normalizaition. So this is a subtle difference that can be missed during debugging
  (before printing, terms and theorems can be \<^emph>\<open>not\<close> in their normal form that is ultimately displayed to the user).
\<close>
text \<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.forall_elim\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>term\<close> : \<^ML_type>\<open>cterm\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  LFC (meta-) \<^emph>\<open>quantifier instantiation\<close> or (meta-) \<^emph>\<open>forall elimination\<close> rule.
  Instantiates the top-level meta-universal
  quantifier \<open>\<And>\<close> according to the rule \<open>(\<And> x. P x) \<Longrightarrow> P y\<close> with the term \<open>y\<close>=\<open>term\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.equal_intr\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>AB\<close> : \<^ML_type>\<open>thm\<close>)\\
  (\<open>BA\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  The LCF (meta-) \<^emph>\<open>equality introduction\<close> rule \<open>(A \<Longrightarrow> B) \<Longrightarrow> (B \<Longrightarrow> A) \<Longrightarrow> A \<equiv> B\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.equal_elim\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>AB\<close> : \<^ML_type>\<open>thm\<close>)\\
  (\<open>A\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  The LCF \<^emph>\<open>equality elimination\<close> rule \<open>A \<equiv> B \<Longrightarrow> A \<Longrightarrow> B\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.reflexive\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>term\<close> : \<^ML_type>\<open>cterm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.symmetric\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.transitive\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>AB\<close> : \<^ML_type>\<open>thm\<close>)\\
  (\<open>BC\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  The usual LCF inference rules for meta-equality \<open>\<equiv>\<close> (reflexivity, symmetry and transitivity as for any equivalence
  relation).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.combination\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>fg\<close> : \<^ML_type>\<open>thm\<close>)\\
  (\<open>tu\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  A designated LCF rule for \<^emph>\<open>combination\<close>: \<open>f \<equiv> g \<Longrightarrow> t \<equiv> u \<Longrightarrow> f t \<equiv> g u\<close>. Despite availability of this rule,
  the transitivity rule is offered as a separate rule for
  efficiency reasons to avoid higher-order unification when possible (consider \<open>f = g = (\<lambda> x. a \<equiv> x)\<close>,
  then transitivity is just an instance of combination modulo equality elimination).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>conv\<close> = \<^ML_type>\<open>cterm -> thm\<close>\\
  A type of \<^emph>\<open>converters\<close> i.\,e. functions that return theorems about some \<^emph>\<open>equivalent\<close>
  transformations of certified terms, e.\,g.
  alpha, beta or eta-normalization. The functions normally return
  a theorem of the form \<open>t \<equiv> t'\<close>, where \<open>t'\<close> is the term \<open>t\<close> after the transformation.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.beta_conversion\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>full\<close> : \<^ML_type>\<open>bool\<close>) :\\
  \<^ML_type>\<open>conv\<close>
  \end{tabular}\\
  A converter for beta-normalization. If \<open>full\<close> is \<^ML>\<open>false\<close>, just performs the reduction of the top-level beta-redex
  (\<open>(\<lambda> x. f x) y \<leadsto> f y\<close>, the term \<^emph>\<open>must be\<close> such a redex). If \<open>full\<close> is \<^ML>\<open>true\<close>, performs \<^emph>\<open>full\<close> beta-normalization,
  in this case the term \<^emph>\<open>may\<close> already be beta-normal.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Conv.fconv_rule\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>conv\<close> : \<^ML_type>\<open>conv\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  LCF \<^emph>\<open>forward conversion\<close> rule. Essentially, just an equality elimination rule for the theorems\\
  \<open>conv (\<close>\<^ML>\<open>Thm.cprop_of\<close> \<open>thm)\<close> and \<open>thm\<close>. Semantically, applies converter to a theorem
  (e.\,g. beta-normalizes the statement of the theorem).
\<close>
text \<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Global_Theory.get_thm\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>)\\
  (\<open>name\<close> : \<^ML_type>\<open>xstring\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Lookup previously saved theorem in a theory by name
  (the eXternal name, therefore \<^ML_type>\<open>xstring\<close>, which is just an alias of \<^ML_type>\<open>string\<close>).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>@{thm name}\<close> : \<^ML_type>\<open>thm\<close>\\
  A convenience quotation to retrieve the theorem by name from the current theory
  (where the ML code is being executed).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Global_Theory.store_thm\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>def\<close> : \<^ML_type>\<open>binding * thm\<close>)\\
  (\<open>thy\<close> : \<^ML_type>\<open>theory\<close>) :\\
  \<^ML_type>\<open>thm * theory\<close>
  \end{tabular}\\
  Store the theorem \<open>snd def\<close> in the theory \<open>thy\<close> by name. The name should be supplied with the location of the
  theorem definition and other supplementary technical information, thus forming a \<^emph>\<open>binding\<close>.

  \<^bigskip>

  \marginsymbol
  \<open>\<^binding>\<open>name\<close>\<close> : \<^ML_type>\<open>binding\<close>\\
  Returns a binding for a given name with the location information pointing at the location of that quotation itself.

  \<^bigskip>

  To modify the current theory, use the command @{command setup} that accepts an update function of type
  \<^ML_type>\<open>theory -> theory\<close>. For more Isabelle/ML interfaces related to LCF and basic theorem manipulation, you can
  also investigate
  the modules \<^ML_structure>\<open>Thm\<close> (\<^file>\<open>~~/src/Pure/thm.ML\<close> and \<^file>\<open>~~/src/Pure/more_thm.ML\<close>) and
  \<^ML_structure>\<open>Drule\<close> (\<^file>\<open>~~/src/Pure/drule.ML\<close>)
\<close>

subsection \<open>Problems\<close>

text \<open>
  \<^enum> Come up with an approach to represent negation (\<open>\<not>\<close>) in a pure intuitionistic propositional logic such as Pure.
    Note that the logic's signature itself only contains the symbols \<open>\<Longrightarrow>\<close>, \<open>\<And>\<close> and \<open>\<equiv>\<close> (i.\,e.
    no disjunction or negation).
  \<^enum> Come up with an approach to represent disjunction in the same logic Pure.\\
    \<^bold>\<open>Hint\<close>: you can look up the
    definitions of constants \<open>\<not>\<close> and \<open>\<or>\<close> in the HOL object logic in \<^file>\<open>~~/src/HOL/HOL.thy\<close> to dig up some insightful
    ideas!
  \<^enum> Prove the \<^emph>\<open>representation\<close> of the \<^emph>\<open>double negation\<close> rule within meta-logic (the rule itself is \<open>\<not>\<not>A \<equiv> A\<close>).
    Note that Pure is higher order intuitionistic propositional logic, so it doesn't assume axiom of choice (\<open>A \<or> \<not> A\<close>)
    and, yet again, does not even define the negation or disjunction symbols.
    So the axiom of choice should be expressed explicitly as a premise of an implication (i.\,e. we have to prove
    something along the lines of \<open>\<And> A. A \<or> \<not>A \<Longrightarrow> \<not>\<not>?A \<equiv> ?A\<close>, modulo the representation).
  \<^enum> Prove a more convenient version of the same theorem in the form
    \<open>neg \<equiv> \<lambda> a. \<dots> \<Longrightarrow> or \<equiv> \<lambda> a b. \<dots> \<Longrightarrow> \<And> A. or A (neg A)  \<Longrightarrow> neg (neg ?A) \<equiv> ?A\<close>, where the definitions of the
    negation and disjunction symbols are assumed as premises.


\<^bold>\<open>Hint\<close>: Use special quotation \<^ML_text>\<open>\<^print>\<close> (effectful ``universal'' printing function) for debugging and command\\
\<^theory_text>\<open>declare [[ML_print_depth=n]]\<close>\\
to enable deeper printing of Isabelle terms.
\<close>

subsection \<open>Solutions\<close>

subsubsection \<open>Problem 3 (directly contains solutions of problems 1 and 2)\<close>

ML \<open>
  infix 1 or
  val prove_double_negation =
    let
      val neg = rpair \<^cterm>\<open>PROP P\<close> ##> Thm.all \<^context> \<^cterm>\<open>PROP P\<close> #> Drule.mk_implies
      val op or =
        apply2 (rpair \<^cterm>\<open>PROP P\<close> #> Drule.mk_implies) ##>
        rpair \<^cterm>\<open>PROP P\<close> ##>
        Drule.mk_implies #>
        Drule.mk_implies #>
        Thm.all \<^context> \<^cterm>\<open>PROP P\<close>
      val excl_mid = Thm.all \<^context> \<^cterm>\<open>PROP Q\<close> (\<^cterm>\<open>PROP Q\<close> or neg \<^cterm>\<open>PROP Q\<close>)
      val a = \<^cterm>\<open>PROP A\<close>

      val elim =
        excl_mid |>
        Thm.assume |>
        Thm.forall_elim a |>
        Thm.forall_elim a |>
        rpair (Thm.trivial a) |->
        Thm.implies_elim |>
        rpair (a |> neg |> neg) ||>
        Thm.assume ||>
        (rpair (a |> neg) ##> Thm.assume #-> Thm.implies_elim #> Thm.forall_elim a #> Thm.implies_intr (a |> neg)) |->
        Thm.implies_elim |>
        Thm.implies_intr (a |> neg |> neg)
      val intro =
        (a |> neg) |>
        Thm.assume |>
        rpair (Thm.assume a) |->
        Thm.implies_elim |>
        Thm.implies_intr (a |> neg) |>
        Thm.implies_intr a
      val thm =
        Thm.equal_intr elim intro |>
        Thm.implies_intr excl_mid |>
        Drule.generalize ([], ["A"])
    in
      (\<^binding>\<open>double_negation\<close>, thm) |>
      Global_Theory.store_thm #>
      snd
    end
\<close>

setup \<open>prove_double_negation\<close>

abbreviation (output) neg ("\<not> _") where "\<not> Q \<equiv> (PROP Q \<Longrightarrow> (\<And> P. PROP P))"

abbreviation (output) or ("_ \<or> _") where
  "A \<or> B \<equiv> (\<And> P. \<lbrakk>PROP A \<Longrightarrow> PROP P; PROP B \<Longrightarrow> PROP P\<rbrakk> \<Longrightarrow> PROP P)"

thm double_negation

subsubsection \<open>Problem 4\<close>

ML \<open>
  fun prove_double_negation_eqs thy =
    let
      val or_def = \<^cterm>\<open>or \<equiv> \<lambda> A B. (\<And>P. (PROP A \<Longrightarrow> PROP P) \<Longrightarrow> (PROP B \<Longrightarrow> PROP P) \<Longrightarrow> PROP P)\<close>
      val neg_def = \<^cterm>\<open>neg \<equiv> \<lambda> A. (PROP A \<Longrightarrow> (\<And> P. PROP P))\<close>
    in
      Thm.reflexive \<^cterm>\<open>\<lambda> f g. ((\<And> Q. PROP f Q (g Q)) \<Longrightarrow> PROP g (g A) \<equiv> PROP A)\<close> |>
      rpair (Thm.assume or_def) |->
      Thm.combination |>
      rpair (Thm.assume neg_def) |->
      Thm.combination |>
      Thm.symmetric |>
      Conv.fconv_rule (Thm.beta_conversion true) |>
      Drule.generalize ([], ["A"]) |>
      rpair (Global_Theory.get_thm thy "double_negation") |->
      Thm.equal_elim |>
      Thm.implies_intr or_def |>
      Thm.implies_intr neg_def |>
      Drule.generalize ([], ["or", "neg"]) |>
      pair \<^binding>\<open>double_negation_eqs\<close> |>
      rpair thy |->
      Global_Theory.store_thm |>
      snd
   end
\<close>

setup \<open>prove_double_negation_eqs\<close>

thm double_negation_eqs

(*<*)
end
(*>*)
