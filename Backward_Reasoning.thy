(*<*)
theory Backward_Reasoning
  imports Main
begin
(*>*)

section \<open>Backward reasoning\<close>

subsection \<open>Isabelle/ML interfaces\<close>

text \<open>
  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Goal.prove\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>vars\<close> : \<^ML_type>\<open>string list\<close>)\\
  (\<open>asms\<close> : \<^ML_type>\<open>term list\<close>)\\
  (\<open>prop\<close> : \<^ML_type>\<open>term\<close>)\\
  (\<open>tacf\<close> : \<^ML_type>\<open>{prems: thm list, context: Proof.context} -> tactic\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  A convenient shortcut to prove theorems of the form \<open>\<lbrakk>A\<^sub>1 \<^bold>x; \<dots>; A\<^sub>n \<^bold>x\<rbrakk> \<Longrightarrow> B \<^bold>x\<close>, where \<open>\<^bold>x\<close> (\<open>vars\<close>) are the outer
  (would-be schematic) variables of the theorem to be generalized, \<open>A\<^sub>1 \<^bold>x; \<dots>; A\<^sub>n \<^bold>x\<close> (\<open>asms\<close>) are auxiliary premises
  (\<open>prems\<close>) to be later lifted to assumptions, and \<open>B \<^bold>x\<close> (\<open>prop\<close>) is the conclusion. \<open>context\<close> is the inner context with
  the assumptions explicitly given as premises (\<open>prems\<close>) and the variables properly fixed and assumed. E.\,g.:
\<close>
ML \<open>
  Goal.prove \<^context> ["A", "B"] [\<^prop>\<open>A\<close>] \<^prop>\<open>B \<Longrightarrow> A \<and> B\<close>
    (fn {context=ctxt, prems=[A]} =>
          HEADGOAL (REPEAT_ALL_NEW (resolve_tac ctxt [@{thm conjI}, A]) THEN' assume_tac ctxt)
       | _ => raise Match)
\<close>
text \<open>
  The resulting theorem is \<open>?A \<Longrightarrow> ?B \<Longrightarrow> ?A \<and> ?B\<close>.
  This can be illustrated as follows:\\
  context:\\
  \tab{}A\\
  state:\\
  \tab{}\begin{tabular}{l}
  \<open>B \<Longrightarrow> A \<and> B\<close>\\
  \hline
  \<open>B \<Longrightarrow> A \<and> B\<close>
  \end{tabular}\\
  Or, for simplicity: \<open>A \<turnstile> B \<Longrightarrow> A \<and> B\<close>. What's below the line (the outermost implication) is always the original
  conjecture, so it's omitted for brevity. Meanwhile, the above part is gradually transformed by the tactics. When the
  above part becomes empty (which is equivalent to identical truth), the conjecture below the line becomes a theorem.
  The proof proceeds as follows:\\
  \tab\begin{tabular}{ll}
  \<open>A \<turnstile> B \<Longrightarrow> A \<and> B\<close>&           \<open>\<Midarrow>resolve with \<open>conjI\<close>\<Rightarrow>\<close>\\
  \<open>A \<turnstile> B \<Longrightarrow> A &&& B \<Longrightarrow> B\<close>&   \<open>\<Midarrow>resolve head goal with \<open>A\<close>\<Rightarrow>\<close>\\
  \<open>A \<turnstile> B \<Longrightarrow> B\<close>&               \<open>\<Midarrow>assume\<Rightarrow>\<close>\\
  \<open>A \<turnstile> \<top>\<close>& \<open>\<top>\<close> designates an empty outermost premise
  \end{tabular}\\
  After the proof, the premise \<^term>\<open>A\<close> is lifted to an assumption \<open>A \<Longrightarrow> _\<close> and the variables \<open>A\<close> and \<open>B\<close> are
  generalized and become schematic.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>tactic\<close> = \<^ML_type>\<open>thm -> thm Seq.seq\<close> \\
  The Isabelle/ML type for \<^emph>\<open>tactics\<close> i.\,e. functions non-deterministically transforming the goal state e.\,g.\\
  \<open>B \<Longrightarrow> B\<close> is transformed to \<open>\<top>\<close> by the \<^ML>\<open>assume_tac\<close> or \<open>x \<in> {u} \<Longrightarrow> y \<in> {v} \<Longrightarrow> T\<close> is transformed to either
  \<open>y \<in> {v} \<Longrightarrow> x = u \<Longrightarrow> T\<close> or \<open>x \<in> {u} \<Longrightarrow> y = v \<Longrightarrow> T\<close> by \<^ML>\<open>eresolve_tac \<^context> [@{thm singletonE}]\<close>. The
  resulting \<^emph>\<open>lazily computed\<close> sequence contains all possible resulting states emerging from applying the tactic and
  can be potentially infinite.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Local_Defs.unfold_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Unfolds definitions represented by the specified theorems (\<open>thms\<close>) as equalities (\<open>LHS = RHS\<close> or\\ \<open>LHS \<equiv> RHS\<close>)
  \<^emph>\<open>everywhere\<close> in \<^emph>\<open>all\<close> subgoals of the proof state.
\<close>
text\<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>assume_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Solves the subgoal with number \<open>goal\<close> (counted starting from 1) by unifying its conclusion with one of the premises
  e.\,g. \<open>A \<Longrightarrow> \<dots> \<Longrightarrow> D \<Longrightarrow> \<dots> \<Longrightarrow> Z \<Longrightarrow> D\<close>, i.\,e. corresponds to the use of a trivial implication of the
  form \<open>A \<Longrightarrow> A\<close>. It's considered a better practice to specify the subgoal index implicitly using some tactical,
  such as \<^ML>\<open>HEADGOAL\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>HEADGOAL\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tac\<close> : \<^ML_type>\<open>int -> tactic\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Applies the tactic \<open>tac\<close> to the first subgoal of the proof state.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>resolve_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Transforms subgoal with index \<open>goal\<close> by resolving its conclusion with the conclusion of one of the theorems
  in the list \<open>thms\<close>. Tries all possible unifiers, then all possible theorems in the list in order. The premises
  of the theorems in \<open>thms\<close> become new subgoals \<^emph>\<open>replacing\<close> the target subgoal. E.\,g.
  \<^ML>\<open>resolve_tac \<^context> [@{thm UnI1}, @{thm UnI2}]\<close> will transform \<open>x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> A \<union> B \<close> to either
  \<open>x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A\<close> or \<open>x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> B\<close> (in that order).
  \<^ML>\<open>resolve_tac \<^context> [@{thm IntI}]\<close>, on
  the other hand, will transform \<open>x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A \<inter> B\<close> to
  \<open>x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A &&& x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> B\<close> (two emerging subgoals). The tactic is often used
  in combination with \<^ML>\<open>assume_tac\<close> and the \<^ML>\<open>THEN\<close> combinator.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 1 THEN\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>(THEN)\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tacs\<close> : \<^ML_type>\<open>tactic * tactic\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Sequential combination of tactics. Applies two tactics in order, but returns the sequence of all
  possible \<^emph>\<open>successful\<close> applications of the second tactic to one of the resulting states returned by the first one.
  Thus it automatically filters out unsuccessful attempts and provides a mechanism for proof search with backtracking.
  E.\,g. \<^ML>\<open>HEADGOAL (resolve_tac \<^context> [@{thm UnI1}, @{thm UnI2}]) THEN HEADGOAL (assume_tac \<^context>)\<close> will
  succeed on the subgoal \<open>x \<in> B \<Longrightarrow> x \<in> A \<union> B\<close>, even though the first attempt will result in an intermediate state
  \<open>x \<in> B \<Longrightarrow> x \<in> A\<close>, which cannot be solved by assumption.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 1 THEN'\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>(THEN')\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tacs\<close> : \<^ML_type>\<open>(int -> tactic) * (int -> tactic)\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  A version of \<^ML>\<open>THEN\<close> for goal-specific tactics (with a \<open>goal\<close> parameter), equivalent to
  \<open>fn x => tac\<^sub>1 x THEN tac\<^sub>2 x\<close> i.\,e. the goal index is always the same.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 1 THEN_ALL_NEW\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>(THEN_ALL_NEW)\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tacs\<close> : \<^ML_type>\<open>(int -> tactic) * (int -> tactic)\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Structural combination of tactics: apply the second tactic to all subgoals emerging from application of the first
  one. Supports backtracking and enumerates all possible outcomes.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>REPEAT_ALL_NEW\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tac\<close> : \<^ML_type>\<open>(int -> tactic)\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Repeats application of \<open>tac\<close> as in \<open>tac THEN_ALL_NEW tac \<dots> THEN_ALL_NEW tac\<close> until an empty sequence is returned,
  then returns the last resulting state. Also supports backtrackingm thus returning all possible terminal states (where
  no further application of the tactic is possible anymore).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>solve_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  A shorthand for \<open>resolve_tac ctxt thms THEN_ALL_NEW assume_tac ctxt\<close>. Convenient for applying 
  theorems with several premises that can be solved by assumption.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>hyp_subst_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Rewrite all assumptions and the conclusion of the subgoal \<open>goal\<close> using the first encountered
  assumption of the form \<open>x = t\<close>, where \<open>x\<close> is a variable and \<open>t\<close> is a term. Also \<^emph>\<open>delete\<close> the assumption
  \<open>x = t\<close> afterwards. E.\,g. \<open>x = y \<Longrightarrow> P (f x) \<Longrightarrow> C\<close> becomes \<open>P (f y) \<Longrightarrow> C\<close>. For a more sophisticated substitutions
  using assumed equalities, a full higher-order unification should be employed using the simplifier or the
  following \<^ML>\<open>eresolve_tac\<close> tactic.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>eresolve_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Applies an \<^emph>\<open>elimination rule\<close> of the form \<open>A \<Longrightarrow> (\<And> \<^bold>x. B \<^bold>x \<Longrightarrow> ?T \<^bold>z) \<Longrightarrow> ?T \<^bold>y\<close> by replacing the subgoal
  \<open>A \<Longrightarrow> C \<Longrightarrow> D \<^bold>y\<close>
  with the subgoal \<open>\<And> \<^bold>x. C \<Longrightarrow> B \<^bold>x \<Longrightarrow> D \<^bold>z\<close>, i.~e. the meta-quantified variables \<open>\<^bold>x\<close> are introduced into the resulting
  subgoal, the context \<open>B \<^bold>x\<close> is assumed, the goal is substituted with the variables \<open>\<^bold>z\<close> and the assumption \<open>A\<close> is
  \<^emph>\<open>deleted\<close>. E.\,g. resolving with
  the theorem \<^prop>\<open>\<lbrakk>s = t; P s\<rbrakk> \<Longrightarrow> P t\<close> will substitute \<open>t\<close> for \<open>s\<close> in the conclusion of the subgoal \<open>goal\<close>
  given the assumption \<open>s = t\<close>, whereas resolving with the theorem \<^prop>\<open>\<lbrakk>s = t; P s; P t \<Longrightarrow> T\<rbrakk> \<Longrightarrow> T\<close> will
  substitute \<open>t\<close> for \<open>s\<close> in \<^emph>\<open>some\<close> of the assumptions given the same assumption \<open>s = t\<close>. Again, the tactic returns
  a lazy sequence of all possible resulting proof states (arising due to non-deterministic unification, choice of
  assumptions for resolution or choice of the theorem from the list \<open>thms\<close>). The tactic is often combined with the
  following theorem transformer function \<^ML>\<open>make_elim\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>make_elim\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Transforms a theorem of the form \<open>A \<Longrightarrow> B\<close> into an elimination rule \<open>A \<Longrightarrow> (B \<Longrightarrow> T) \<Longrightarrow> T\<close>. Combining this
  with \<^ML>\<open>resolve_tac\<close> and \<^ML>\<open>assume_tac\<close> is essentially equivalent to the following \<^emph>\<open>forward resolution\<close> tactic.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>forward_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Forward resolution. Try to solve the \<^emph>\<open>major\<close> (first) premise of a theorem in \<open>thms\<close> by assumption,
  then return the subgoals
  for solving other (\<^emph>\<open>minor\<close>) premises and the subgoal with the conclusion of the theorem added as an assumption.
  E.\,g. given the state \<open>x = y \<Longrightarrow> y = z \<Longrightarrow> C\<close>, forward resolution \<^ML>\<open>forward_tac \<^context> [@{thm trans}]\<close>
  (@{thm trans[no_vars]}) will result in
  two subgoals: \<open>x = y \<Longrightarrow> y = z \<Longrightarrow> y = ?t &&& x = y \<Longrightarrow> y = z \<Longrightarrow> x = ?t \<Longrightarrow> C\<close>. Here \<open>?t\<close> is a schematic variable
  and it can be further instantiated to any term e.\,g. by some resolution tactic such as \<^ML>\<open>assume_tac\<close>. Note that
  the schematic variable occurring in the proof state (the goal) are \<^emph>\<open>existentially\<close> quantified i.\,e. it's sufficient
  to provide a proof with \<^emph>\<open>some\<close> instantiation of such a variable.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Method.insert_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Simply insert the theorems \<open>thms\<close> as assumptions into the specified subgoal \<open>goal\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>EqSubst.eqsubst_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>occs\<close> : \<^ML_type>\<open>int list\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Given a selection of possible conditional equalities of the form \<open>C \<Longrightarrow> LHS = RHS\<close>,
  rewrite the specified occurrences \<open>occs\<close> of the
  \<open>LHS\<close> in the \<^emph>\<open>conclusion\<close> of the subgoal \<open>goal\<close> to \<open>RHS\<close>, leaving the pre-condition \<open>C\<close> as a new subgoal. Only the
  first applicable theorem in \<open>thms\<close> is used. The
  occurrences are counted starting from \<open>1\<close>, \<open>0\<close> designated \<^emph>\<open>any\<close> occurrence. The subgoal for the pre-condition \<open>C\<close>
  is posed \<^emph>\<open>before\<close> the substituted initial subgoal \<open>goal\<close>. E.\,g. applying
  \<^ML>\<open>EqSubst.eqsubst_tac \<^context> [0] [@{thm arg_cong[where f=F]}]\<close> (@{thm arg_cong})
  to the subgoal \<open>x = t \<Longrightarrow> P (F x) = P (F t)\<close> will result
  in a state \<open>x = t \<Longrightarrow> ?x = ?y &&& x = t \<Longrightarrow> P (F ?y) = P (F t)\<close>. The instantiation \<open>[where f=F]\<close> can be preformed
  using the function \<^ML>\<open>infer_instantiate'\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>infer_instantiate'\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>subs\<close> : \<^ML_type>\<open>cterm option list\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Instantiate the theorem \<open>thm\<close> with the terms \<open>subs\<close>, substituting the schematic variables from left to right
  and leaving the unspecified variables (designated as \<open>NONE\<close>s) as is.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>EqSubst.eqsubst_asm_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>occs\<close> : \<^ML_type>\<open>int list\<close>)\\
  (\<open>thms\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Same as \<^ML>\<open>EqSubst.eqsubst_tac\<close>, but performs substitutions in the assumptions of the subgoal \<open>goal\<close>.
\<close>
text\<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Induct_Tacs.case_tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>term\<close> : \<^ML_type>\<open>string\<close>)\\
  (\<open>fixes\<close> : \<^ML_type>\<open>(binding * string option * mixfix) list\<close>)\\
  (\<open>rule\<close> : \<^ML_type>\<open>thm option\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Applies case-splitting/induction rule instantiated \<^emph>\<open>within local subgoal context\<close>. Normally, an induction or
  case-splitting rule is just an elimination rule of the form \<open>A \<Longrightarrow> (B \<Longrightarrow> T) \<Longrightarrow> (C \<Longrightarrow> T) \<Longrightarrow> T\<close>. E.\,g.
  @{thm finite_induct[no_vars]} (\<open>@{thm finite_induct\<close>). However, there are two problems regarding
  instantiation of such elimination rules:
  \<^item> First, the substituted terms e.\,g. the term for the finite set \<open>F\<close>, may depend on the local variables bound in the
    current subgoal, such as in \<open>\<And> u v. finite u \<Longrightarrow> finite v \<Longrightarrow> P (F u v)\<close>, where the desired term \<open>F u v\<close> depends on
    bound variables \<open>u\<close> and \<open>v\<close> that \<^emph>\<open>do not exist\<close> in the outer context \<open>ctxt\<close> or \<open>\<^context>\<close> and therefore cannot be
    specified by usual means.
  \<^item> Second, the substituted terms may contain nested schematic variables e.\,g. \<open>P (F ?u ?v)\<close> that are to be
    instantiated later, possibly implicitly by applying some resolution tactics such as \<^ML>\<open>assume_tac\<close>. This is useful
    for specifying big complex terms by only outlining their external skeleton.


  To address those issues, the term \<open>term\<close> for case analysis is passed as a \<^emph>\<open>string\<close>, which is interpreted in the
  special local subgoal context extended with declaration of subgoal-specific quantified variables and
  fixed constants provided in \<open>fixes\<close> that are later turned into schematic variables.
  The case-splitting/induction rule can be omitted
  if the default rule for the type of the term \<open>term\<close> is used (e.\,g. the rule \<open>@{thm case_split}\<close>
  (@{thm case_split[no_vars]}) for type \<^typ>\<open>bool\<close>).
  The default rules are specified using the attribute @{attribute cases}.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Lin_Arith.tac\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  Prove the subgoal \<open>goal\<close> by solving a system of linear arithmetic inequalities. The conjunction of the
  assumptions with the negation of the conclusion must be unsatisfiable. Supports all types of class
  \<^class>\<open>linordered_idom\<close>, including \<open>int\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>attribute\<close> = \<^ML_type>\<open>Context.generic * thm -> Context.generic option * thm option\<close> \\
  A type of \<^emph>\<open>attributes\<close>, i.~e. functions that simultaneously transform a theorem and the corresponding context.
  Attributes can both modify the theorem (e.\,g. they can transform it into an elimination rule, atomize, rulify etc.)
  and change some components of the shared state in the context e.\,g. by registring a case-splitting rule or
  symmetry rule.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.proof_attributes\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>atts\<close> : \<^ML_type>\<open>attribute list\<close>) \\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) \\
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>) :\\
  \<^ML_type>\<open>thm * Proof.context\<close>
  \end{tabular}\\
  A function to apply a list of attributes \<open>atts\<close> (in order) in the proof context \<open>ctxt\<close> and obtain the transformed
  theorem (the same theorem, if the attribute returns \<open>NONE\<close>) and the context.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Calculation.symmetric\<close> : \<^ML_type>\<open>attribute\<close>\\
  This attribute transforms theorems with an equality in the conclusion by swapping the sides of the equality.
  \<open>A \<Longrightarrow> x = y\<close> will become \<open>A \<Longrightarrow> y = x\<close>. Useful in combination with substitution tactics such as
  \<^ML>\<open>EqSubst.eqsubst_tac\<close> and \<^ML>\<open>EqSubst.eqsubst_asm_tac\<close>. The particular equality is specified using an attribute
  @{attribute sym} for a theorem of the form \<open>a = b \<Longrightarrow> b = a\<close>, so the attribute is slightly more general and,
  in particular, also supports disequalities (\<open>a \<noteq> b \<Longrightarrow> b \<noteq> a\<close>).
\<close>
text \<open>
  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>ALLGOALS\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tac\<close> : \<^ML_type>\<open>int -> tactic\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  A tactic combinator (\<^emph>\<open>tactical\<close>) to apply a subgoal-specific tactic (with a \<open>goal\<close> parameter) to all subgoals
  of the current proof state.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>RANGE\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tacs\<close> : \<^ML_type>\<open>(int -> tactic) list\<close>)\\
  (\<open>goal\<close> : \<^ML_type>\<open>int\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  A tactical that applies subgoal-specific tactics to the \<^emph>\<open>corresponding\<close> subgoals, starting from the subgoal
  at index \<open>goal\<close>. This is quite convenient to convey proof trees with several sub-branches to clearly delimit
  the proof branches from each other. The \<open>i\<close>-th element of the list \<open>tacs\<close> (counting from \<open>0\<close>) is applied to
  the subgoal with index \<open>goal + i\<close>, where subgoals are counted from \<open>1\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>EVERY\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tacs\<close> : \<^ML_type>\<open>tactic list\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  A shortcut for \<open>tac\<^sub>1 THEN tac\<^sub>2 ... THEN tac\<^sub>n\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>EVERY'\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>tac\<close> : \<^ML_type>\<open>('a -> tactic) list\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>) :\\
  \<^ML_type>\<open>tactic\<close>
  \end{tabular}\\
  A shortcut for \<open>fn i \<Rightarrow> tac\<^sub>1 i THEN tac\<^sub>2 i ... THEN tac\<^sub>n i\<close> (consequtive application of tactics to the same subgoal).

  \<^bigskip>
  More tactics can be found in the module \<open>Tactic\<close> (implemented in file \<^file>\<open>~~/src/Pure/tactic.ML\<close>) and throughout
  the Isabelle sources, usually with the suffix \<open>_tac\<close>. More
  tacticals can be found in module \<open>Tactical\<close> (implemented in \<^file>\<open>~~/src/Pure/tactical.ML\<close>).
\<close>

subsection \<open>Theorems\<close>

text \<open>
\begin{tabular}{rl}
  \<open>set_eq_iff\<close>:& @{thm set_eq_iff[no_vars]}\\
  \<open>not_all\<close>:& @{thm not_all[no_vars]}\\
  \<open>HOL.nnf_simps(5)\<close>:& @{thm HOL.nnf_simps(5)[no_vars]}\\
  \<open>subst\<close>:& @{thm subst[no_vars]}\\
  \<open>Diff_iff\<close>:& @{thm Diff_iff[no_vars]}\\
  \<open>DiffI\<close>:& @{thm DiffI[no_vars]}\\
  \<open>someI\<close>:& @{thm someI[no_vars]}\\
  \<open>exE\<close>:& @{thm exE[no_vars]}\\
  \<open>notE\<close>:& @{thm notE[no_vars]}\\
  \<open>emptyE\<close>:& @{thm emptyE[no_vars]}\\
  \<open>UnE\<close>:& @{thm UnE[no_vars]}\\
  \<open>disjE\<close>:& @{thm disjE[no_vars]}\\
  \<open>conjE\<close>:& @{thm conjE[no_vars]}\\
  \<open>IntE\<close>:& @{thm IntE[no_vars]}\\
  \<open>IntI\<close>:& @{thm IntI[no_vars]}\\
  \<open>conj_commute\<close>:& @{thm conj_commute[no_vars]}\\
  \<open>singletonE\<close>:& @{thm singletonE[no_vars]}\\
  \<open>singletonI\<close>:& @{thm singletonI[no_vars]}\\
\end{tabular}
\<close>

subsection \<open>Problems\<close>

text \<open>
  \<^enum> Define (using \<^ML>\<open>Sign.declare_const_global\<close> and \<^ML>\<open>Global_Theory.add_defs\<close>)
    an auxiliary skolem function \<open>w\<close> arising from skolemization of the theorem
    \<^prop>\<open>s \<noteq> t \<Longrightarrow> \<exists> x. x \<in> s - t \<or> x \<in> t - s\<close>. Use the Hilbert epsilon operator \<^const>\<open>Eps\<close> that has a designated
    syntax \<^term>\<open>SOME x. P x\<close>.
  \<^enum> Prove the following theorem: \<open>set_neqD\<close>: \<^prop>\<open>s \<noteq> t \<Longrightarrow> w s t \<in> s \<and> w s t \<notin> t \<or> w s t \<notin> s \<and> w s t \<in> t\<close> for the
    skolem function \<open>w\<close> above. Use backward (tactical) reasoning in pure Isabelle/ML and the function \<^ML>\<open>Goal.prove\<close>.
  \<^enum> Prove the following theorem: \<open>sample1\<close>: \<^prop>\<open>x \<in> {1} \<union> {2} \<Longrightarrow> x \<le> (2 :: int)\<close> using tactical reasoning.
  \<^enum> Prove an auxiliary property \<open>member_neqI\<close>: \<^prop>\<open>x \<in> A \<Longrightarrow> y \<notin> A \<Longrightarrow> x \<noteq> y\<close> using tactical reasoning.
  \<^enum> Using the auxiliary properties \<open>set_neqD\<close> and \<open>member_neqI\<close>, prove the following theorem:
    \<^prop>\<open>\<lbrakk>4 < u; u < 6; u \<in> x \<union> y; x \<inter> {5 :: int} \<noteq> {5}; z = {}\<rbrakk> \<Longrightarrow> y - z \<noteq> {}\<close>. The proof is non-trivial and
    the corresponding proof tree can be found in the paper \<open>Calogero G. Zarba. Combining Sets with Elements\<close> on page
    \<open>13\<close>. Use tactical reasoning and structure the proof tree using the \<^ML>\<open>RANGE\<close> and \<^ML>\<open>EVERY'\<close> tacticals.

You can help yourself by using tactical reasoning in Isabelle GUI with commands @{command apply} and @{command by}.
Also, a special tactic @{method tactic} can be used to apply a tactic implemented in pure ML e.\,g.:
\<close>
lemma "A \<Longrightarrow> A" apply (tactic \<open>HEADGOAL (assume_tac \<^context>)\<close>) done

subsection \<open>Solutions\<close>

setup \<open>Sign.declare_const_global ((\<^binding>\<open>w\<close>, \<^typ>\<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a\<close>), NoSyn) #> snd\<close>

setup \<open>
   pair
    (\<^binding>\<open>w_def\<close>,
     \<^term>\<open>w s t \<equiv> SOME x. x \<in> s - t \<or> x \<in> t - s\<close>) #>>
   Thm.simple_fact #->
   Global_Theory.add_defs false #>
   snd
\<close>

\<comment> \<open>
\<^theory_text>\<open>
lemma set_neqD:
  "s \<noteq> t \<Longrightarrow> w s t \<in> s \<and> w s t \<notin> t \<or> w s t \<notin> s \<and> w s t \<in> t"
  apply (unfold set_eq_iff not_all HOL.nnf_simps(5))
  apply (elim exE)
  apply (subst (asm) (2) conj_commute)
  apply (subst (2) conj_commute)
  apply (unfold w_def Diff_iff[symmetric])
  by (intro someI)
\<close>
\<close>

ML \<open>
  val prove_set_neqD =
    Goal.prove \<^context> ["s", "t"] []
      \<^prop>\<open>s \<noteq> t \<Longrightarrow> w s t \<in> s \<and> w s t \<notin> t \<or> w s t \<notin> s \<and> w s t \<in> t\<close>
      (fn { context=ctxt, ... } =>
        Local_Defs.unfold_tac ctxt [@{thm set_eq_iff}, @{thm not_all}, @{thm HOL.nnf_simps(5)}] THEN
        HEADGOAL (eresolve_tac ctxt [@{thm exE}]) THEN
        HEADGOAL (EqSubst.eqsubst_asm_tac ctxt [2] [@{thm conj_commute}]) THEN
        HEADGOAL (EqSubst.eqsubst_tac ctxt [2] [@{thm conj_commute}]) THEN
        Local_Defs.unfold_tac
          ctxt
          [@{thm w_def}, Thm.proof_attributes [Calculation.symmetric] @{thm Diff_iff} ctxt |> fst] THEN
        HEADGOAL (solve_tac ctxt [@{thm someI}])) |>
    pair \<^binding>\<open>set_neqD\<close> |>
    Global_Theory.store_thm #>
    snd
\<close>

setup \<open>prove_set_neqD\<close>
thm set_neqD

\<comment> \<open>
\<^theory_text>\<open>
lemma sample1: "x \<in> {1} \<union> {2} \<Longrightarrow> x \<le> (2 :: int)"
  apply (elim UnE singletonE)
  by (linarith)+
\<close>
\<close>

ML \<open>
  val prove_sample1 =
    Goal.prove \<^context> ["x"] []
      \<^prop>\<open>x \<in> {1} \<union> {2} \<Longrightarrow> x \<le> (2 :: int)\<close>
      (fn { context=ctxt, ... } =>
        HEADGOAL (REPEAT_ALL_NEW (eresolve_tac ctxt [@{thm UnE}, @{thm singletonE}])) THEN
        ALLGOALS (Lin_Arith.tac ctxt)) |>
    pair \<^binding>\<open>sample1\<close> |>
    Global_Theory.store_thm #>
    snd
\<close>

setup \<open>prove_sample1\<close>
thm sample1

\<comment> \<open>
\<^theory_text>\<open>
lemma member_neqI: "x \<in> A \<Longrightarrow> y \<notin> A \<Longrightarrow> x \<noteq> y"
  apply (cases "x = y")
   apply hypsubst
  by (erule (1) notE)
\<close>
\<close>

ML \<open>
  val prove_member_neqI =
    Goal.prove \<^context> ["x", "y", "A", "B"] []
      \<^prop>\<open>x \<in> A \<Longrightarrow> y \<notin> A \<Longrightarrow> x \<noteq> y\<close>
      (fn { context=ctxt, ... } =>
        HEADGOAL (Induct_Tacs.case_tac ctxt "x = y" [] NONE) THEN
        HEADGOAL (hyp_subst_tac ctxt) THEN
        HEADGOAL (eresolve_tac ctxt [@{thm notE}]) THEN
        ALLGOALS (assume_tac ctxt)) |>
    pair \<^binding>\<open>member_neqI\<close> |>
    Global_Theory.store_thm #>
    snd
\<close>

setup \<open>prove_member_neqI\<close>

\<comment> \<open>
\<^theory_text>\<open>
lemma sample2: "\<lbrakk>4 < u; u < 6; u \<in> x \<union> y; x \<inter> {5 :: int} \<noteq> {5}; z = {}\<rbrakk> \<Longrightarrow> y - z \<noteq> {}"
  apply (elim UnE set_neqD[elim_format])
   apply (elim disjE conjE IntE)
    apply (erule (1) notE)
   apply (elim singletonE)
   apply (insert singletonI[of 5])
   apply (cases "5 \<in> x")
    apply (frule (1) IntI[where A=x and B="{5}"])
    apply (frule (1) member_neqI)
    apply linarith
   apply (cases "u = 5")
    apply hypsubst
    apply (erule (1) notE)
   apply linarith
  apply (cases "u \<in> z")
   apply hypsubst
   apply (erule emptyE)
  apply (frule (1) DiffI)
  apply (intro notI)
  apply (erule (1) subst[where P="\<lambda> x. _ \<in> x", elim_format])
  apply (erule emptyE)
  done
\<close>
\<close>

ML \<open>
  val prove_sample2 =
    Goal.prove \<^context> ["u", "x", "y", "z"] []
      \<^prop>\<open>\<lbrakk>4 < u; u < 6; u \<in> x \<union> y; x \<inter> {5 :: int} \<noteq> {5}; z = {}\<rbrakk> \<Longrightarrow> y - z \<noteq> {}\<close>
      (fn { context=ctxt, ... } =>
        HEADGOAL (REPEAT_ALL_NEW (eresolve_tac ctxt [@{thm UnE}, make_elim @{thm set_neqD}])) THEN
        HEADGOAL (REPEAT_ALL_NEW (eresolve_tac ctxt [@{thm disjE}, @{thm conjE}, @{thm IntE}])) THEN
        HEADGOAL
          (RANGE
            [solve_tac ctxt [@{thm notE}],
             EVERY'
               [eresolve_tac ctxt [@{thm singletonE}],
                Method.insert_tac ctxt [@{thm singletonI} |> infer_instantiate' ctxt [SOME \<^cterm>\<open>5 :: int\<close>]],
                Induct_Tacs.case_tac ctxt "5 \<in> x" [] NONE,
                RANGE
                  [EVERY'
                    [forward_tac ctxt [@{thm IntI}],
                     assume_tac ctxt,
                     forward_tac ctxt [@{thm member_neqI}],
                     assume_tac ctxt,
                     Lin_Arith.tac ctxt],
                   EVERY'
                    [forward_tac ctxt [@{thm member_neqI}],
                     assume_tac ctxt,
                     Lin_Arith.tac ctxt]]],
             
             EVERY'
               [Induct_Tacs.case_tac ctxt "u \<in> z" [] NONE,
                RANGE
                  [EVERY'
                    [hyp_subst_tac ctxt,
                     eresolve_tac ctxt [@{thm emptyE}]],
                   EVERY'
                    [forward_tac ctxt [@{thm DiffI}],
                     assume_tac ctxt,
                     resolve_tac ctxt [@{thm notI}],
                     eresolve_tac ctxt [@{thm subst} |> make_elim],
                     assume_tac ctxt,
                     eresolve_tac ctxt [@{thm emptyE}]]]]])) |>
    pair \<^binding>\<open>sample2\<close> |>
    Global_Theory.store_thm #>
    snd
\<close>

setup \<open>prove_sample2\<close>
thm sample2

end