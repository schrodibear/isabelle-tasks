theory Forward_Reasoning
  imports Main
begin

section \<open>Forward (elim-) composition and resolution\<close>

subsection \<open>Isabelle/ML interfaces\<close>
text \<open>
  \marginsymbol
  \<^ML_text>\<open>type\<close> \<^ML_type>\<open>'a Seq.seq\<close>\\
  An abstract type of lazily evaluated unbounded sequences. Most significant difference form Haskell lists
  is that the ``thunks'' \<^emph>\<open>are not memoized\<close>, that is the values of the elements \<^emph>\<open>are re-evaluated every time\<close>
  they are requested. This is implemented this way doe to efficiency considerations, since memoization increased
  GC pressure.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Seq.make\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>unit -> ('a * 'a Seq.seq) option\<close>) :\\
  \<^ML_type>\<open>'a Seq.seq\<close>
  \end{tabular}\\
  Creates a lazy sequence from a \<^emph>\<open>generator\<close>, the optional thunk of the first element and the rest of the sequence.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Seq.pull\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>'a Seq.seq\<close>) :\\
  \<^ML_type>\<open>('a * 'a Seq.seq) option\<close>
  \end{tabular}\\
  Destructs the sequence by splitting off its head element.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>the\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>opt\<close> : \<^ML_type>\<open>'a option\<close>) :\\
  \<^ML_type>\<open>'a\<close>
  \end{tabular}\\
  Unwraps the optional element, if present, raises \<^ML>\<open>Option\<close> if it is absent.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Seq.hd\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>'a Seq.seq\<close>) :\\
  \<^ML_type>\<open>'a\<close> &= \<^ML_text>\<open>fst (the (Seq.pull s))\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Seq.tl\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>s\<close> : \<^ML_type>\<open>'a Seq.seq\<close>) :\\
  \<^ML_type>\<open>'a\<close> &= \<^ML_text>\<open>snd (the (Seq.pull s))\<close>
  \end{tabular}\\
  Some shortcuts.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Seq.chop\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>n\<close> : \<^ML_type>\<open>int\<close>)\\
  (\<open>s\<close> : \<^ML_type>\<open>'a Seq.seq\<close>)\\
  \<^ML_type>\<open>'a list\<close>
  \end{tabular}\\
  Returns the list of \<^emph>\<open>at most\<close> \<open>n\<close> first elements of the lazy sequence \<open>s\<close>
  (and less elements, if the sequence ends prematurely).

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Seq.filter\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> bool\<close>)\\
  (\<open>s\<close> : \<^ML_type>\<open>'a Seq.seq\<close>)\\
  \<^ML_type>\<open>'a Seq.seq\<close>
  \end{tabular}\\
  Lazily filters the sequence.
\<close>
text \<open>

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.bicompose\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context option\<close>)\\
  (\<open>config\<close> : \<^ML_type>\<open>{flatten : bool, match : bool, incremented : bool}\<close>)\\
  (\<open>rule\<close> : \<^ML_type>\<open>bool * thm * int\<close>)\\
  (\<open>i\<close> : \<^ML_type>\<open>int\<close>)\\
  (\<open>st\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm Seq.seq\<close>
  \end{tabular}\\
  The most basic Isabelle reasoning primitive implementing \<^emph>\<open>forward composition\<close> of a \<^emph>\<open>rule\<close> with a \<^emph>\<open>proof state\<close>.
  Let's define a \<^emph>\<open>proof state\<close> as a theorem of the following form:\\
  \<open>S\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>i \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>n \<Longrightarrow> G\<close>\\
  We'll call the premises \<open>S\<^sub>1, \<dots>, S\<^sub>n\<close> of such a theorem the \<^emph>\<open>subgoals\<close>, and the conclusion the (original)
  \<^emph>\<open>statement\<close>. Meanwhile, let's also define a \<^emph>\<open>rule\<close> in a totally similar way:\\
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>j \<Longrightarrow> \<dots> A\<^sub>m \<Longrightarrow> C\<close>,\\
  where \<open>A\<^sub>j\<close> is called the \<open>j\<close>-th \<^emph>\<open>assumption\<close> of the rule and \<open>C\<close> is called the \<^emph>\<open>conclusion\<close>. Note that \<^emph>\<open>both\<close>
  the subgoals and the assumptions can themselves be arbitrarily complex propositions (of type \<^typ>\<open>prop\<close>) and
  thus \<^emph>\<open>do not\<close> have to be object-logic terms and can include meta-connectives such as \<open>\<Longrightarrow>\<close> and \<open>\<And>\<close>. Thus the
  interpretation of both the proof state and the rule is generally \<^emph>\<open>ambiguous\<close>, since the statement \<open>G\<close> as well as
  the conclusion \<open>C\<close> can include implications, which makes the number of subgoals and premises not fully determined
  solely by the shape of the corresponding theorem. Yet we can still count both the subgoals and the assumptions
  from the left, so any particular positive number is unambiguous (the counting here stats from \<open>1\<close>).

  Now let's consider a rule \<open>r\<close> with (at least) \<open>m\<close> premises. Let's then regard the remaining consequent of the rule
  its conclusion \<open>C\<close> (even if it includes implications). Let's also consider the subgoal \<open>S\<^sub>i\<close> with index \<open>i\<close>.
  Both \<open>C\<close> and \<open>S\<^sub>i\<close> can be considered terms depending on the \<^emph>\<open>schematic variables\<close> (both \<^emph>\<open>term\<close> and \<^emph>\<open>type\<close> variables)
  that occur in them. Let's consider the rule's and the state's variable scopes \<^emph>\<open>together\<close> as if the variables are
  \<^emph>\<open>shared\<close> between them. Now we can intoroduce the notion of a \<^emph>\<open>unifier\<close> \<open>\<theta>\<close>, which is a substitution that makes two
  terms syntactically equal to each other: \<open>\<theta>C \<equiv> \<theta>S\<^sub>i\<close>. Note that in Isabelle we consider \<^emph>\<open>higher-order\<close> unification,
  where terms may contain lambda-abstractions and applications of schematic variables to arbitrary arguments. The
  problem of deciding whether there exists a unifier for two arbitrary such terms is \<^emph>\<open>undecidable\<close> in general, and
  moreover, even if some unifier does exist it may not me unique even up to instantiation. Therefor there's no notion
  of the most general unifier. Instead what we get is a possibly infinite sequence of unifiers. Let's designate
  an arbitrary member of such a sequence as \<open>\<theta>\<^sub>k\<close> and the whole sequence as \<open>\<dots>\<langle>\<theta>\<^sub>k\<rangle>\<dots>\<close>. Now in the default mode, the
  result of the function \<^ML>\<open>Thm.bicompose\<close> applied to a \<open>rule\<close> \<^ML_text>\<open>(false, r, m)\<close> (where \<open>r\<close> has the form
  \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>j \<Longrightarrow> \<dots> A\<^sub>m \<Longrightarrow> C\<close>), a subgoal index \<open>i\<close> and a state \<open>st\<close> (\<open>S\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>i \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>n \<Longrightarrow> G\<close>) is
  the following possibly infinite sequence of theorems:\\
  \<open>\<dots>\<langle>\<theta>\<^sub>kS\<^sub>1 \<Longrightarrow>\<dots>\<Longrightarrow> \<theta>\<^sub>kS\<^bsub>i-1\<^esub> \<Longrightarrow> \<theta>\<^sub>kA\<^sub>1 \<Longrightarrow>\<dots>\<Longrightarrow> \<theta>\<^sub>kA\<^sub>m \<Longrightarrow> \<theta>\<^sub>kS\<^bsub>i+1\<^esub> \<Longrightarrow>\<dots>\<Longrightarrow> \<theta>\<^sub>kS\<^sub>n \<Longrightarrow> \<theta>\<^sub>kG\<rangle>\<dots>\<close>,\\
  given the side-condition that for every substitution \<open>\<theta>\<^sub>k\<close>, \<open>\<theta>\<^sub>kC \<equiv> \<theta>\<^sub>kS\<^sub>i\<close>. As can be seen from that explanation, the
  conclusion \<open>C\<close> of the rule \<open>r\<close> should unify with the \<open>i\<close>-th subgoal \<open>S\<^sub>i\<close> of the state producing a substitution
  of the shared variables that is applied both to the rule and the state before replacing the subgoal \<open>S\<^sub>i\<close> with
  the sequence of assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>m\<close>, \<open>m \<ge> 0\<close>. This is the most general form of the operation that is called
  \<^emph>\<open>composition\<close> of the rule \<open>r\<close> with the state \<open>st\<close> in Isabelle parlance. If not specified otherwise, the default
  values of additional parameters in this operation are assumed to be \<open>m = 0\<close> and \<open>i = 1\<close>.

  Now let's introduce an Isabelle-specific version of such general operation. It's called \<^emph>\<open>elim-composition\<close> and
  is only different from the general composition in that it imposes an additional constraint on the unifiers \<open>\<theta>\<^sub>k\<close>,
  namely: There should exist an assumption \<open>A\<^sub>j\<close>, \<open>1 \<le> j \<le> m\<close> such that it itself has the form\\
  \<open>B\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> B\<^sub>l \<Longrightarrow> B\<close>, where \<open>\<theta>\<^sub>kB\<^sub>p \<equiv> B\<close> for some \<open>1 \<le> p \<le> l\<close>. Intuitively it means that the assumption
  is in a certain way trivially equivalent to identical truth modulo some instantiation of schematic variables. This is
  called \<^emph>\<open>proving by assumption\<close> in Isabelle parlance,
  since the assumption momentarily becomes a new subgoal in the resulting proof state and that emerging subgoal is
  then immediately solved by assumption. At the first glance this support of a rather special case of composition
  may seem rather artificial, but in fact it is provided with the appropriate optimized implementation
  \<^emph>\<open>directly in the proof kernel\<close> itself due to being a very common case in proofs, including the ones produced by
  rather powerful proof methods such as @{method auto}. Actually, the whole composition (and resolution, see below)
  machinery of Isabelle is implemented directly in the kernel due to efficiency considerations, since all the
  manipulations needed to perform the actual composition can themselves be certified within the proof kernel. However,
  the number of inner intermediate kernel interface calls would be quite significant and that would create a very
  unpleasant proof overhead for such a basic proof operation as composition. The elim-composition is enabled by
  changing the \<^emph>\<open>elim\<close> \<^emph>\<open>flag\<close> in the \<open>rule\<close> parameter to \<^ML>\<open>true\<close> i.\,e. \<^ML_text>\<open>(true, r, m)\<close>. This variant
  of composition is mostly relevant for \<^emph>\<open>elimination rules\<close> of the form\\
  \<open>A\<^sub>1\<Longrightarrow>\<dots>\<Longrightarrow> A\<^bsub>m-r\<^esub>\<Longrightarrow> (B\<^bsub>1,1\<^esub> \<Longrightarrow>\<dots>\<Longrightarrow> B\<^bsub>1,l\<^sub>1\<^esub> \<Longrightarrow> ?C)\<Longrightarrow>\<dots>\<Longrightarrow> (B\<^bsub>r,l\<^sub>1\<^esub> \<Longrightarrow>\<dots>\<Longrightarrow> B\<^bsub>r,l\<^sub>r\<^esub> \<Longrightarrow> ?C)\<Longrightarrow> ?C\<close>,\\
  where the whole conclusion is just a single schematic variable \<open>?C\<close> (note that there are still \<open>m\<close> assumptions).
  Obviously, in this case the usual constraint
  \<open>\<theta>\<^sub>k?C \<equiv> \<theta>\<^sub>kS\<^sub>i\<close> often becomes too weak, hence the need for the additional constraint. Note also that there are also
  cases, where even though the conclusion is still a single variable \<open>?C\<close>, no additional constraints are needed. This,
  for instance, is the case for the usual case-splitting rule @{thm case_split}. But in these cases an additional
  manual instantiation of the rule is often necessary (as in most of the corresponding applications
  of the @{method cases} method).

  Now let's consider the other additional configuration options that finely control the composition. The flag
  \<open>flatten\<close> is only relevant for elimination rules and simultaneously enables two things:
  \<^item> Normalization of (meta-) quantifiers in the emerging subgoals \<open>A\<^sub>j\<close> of the form\\
    \<open>\<theta>B\<^sub>i\<^sub>,\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> \<theta>B\<^sub>i\<^sub>,\<^bsub>l\<^sub>i\<^esub> \<Longrightarrow> \<theta>C\<close> into
    the prenex normal form;
  \<^item> Deletion of the \<open>j\<close>-th premise, where \<open>A\<^sub>j\<close> was solved by assumption, from every emerging subgoal \<open>A\<^sub>j\<close>.


  Both of these features are mostly relevant for tactical reasoning that builds upon composition and resolution and
  are also integrated directly into the proof kernel for efficiency. The flag \<open>match\<close> ensures that \<^emph>\<open>all\<close> subgoals
  of the proof state \<open>st\<close>, \<^emph>\<open>including\<close> the subgoal \<open>S\<^sub>i\<close>, remain unchanged by every substitution \<open>\<theta>\<^sub>k\<close>. This
  is treated as an additional constraint on the resulting sequence of unifiers \<open>\<dots>\<langle>\<theta>\<^sub>k\<rangle>\<dots>\<close>. The corresponding
  special case of such unification (where one of the terms remains unchanged by substitution) is called \<^emph>\<open>matching\<close>.
  There are also derived terms such as \<^emph>\<open>match-composition\<close> or \<^emph>\<open>match-elimination\<close>. The semantics of
  the flag \<open>incremented\<close> may seem rather strange, but worth mentioning to avoid some common confusion. The point is
  that schematic term variables in Isabelle are actually treated as \<^emph>\<open>Church-style\<close>, i.\,e. term variables of different
  types are considered different even if they have the same name. For that reason, technically, there is a potential
  for variability in the behavior of composition for term variables that \<^emph>\<open>do not\<close> occur in either \<open>C\<close> or \<open>S\<^sub>i\<close> (as
  well as \<open>B\<^sub>p\<close> or \<open>B\<close> when the elim-flag is enabled). Since the unifier does not contain any explicit
  substitutions for those variables, their \<^emph>\<open>types\<close> can either be paired according to their names and unified
  (\<open>incremented = false\<close>) or left as-is, remaining possibly different from each other and potentially incompatible
  (\<open>incremented = true\<close>). Note, again, that the additional type substitutions here are potentially being imposed
  solely by the coinciding names of the variables rather than being implied by the required
  syntactic equalities of the terms. By the way, setting \<open>increment\<close> to \<open>true\<close> is this function is one
  of only just a few ways to obtain theorems with really Church-style variables in Isabelle, most higher-level
  interfaces actually prevent such cases.

  The only remaining optional parameter is the proof context \<open>ctxt\<close>. Indeed, it
  is optional and only controls the amount of debugging information that can be printed during unification. Dy default
  \<^emph>\<open>no\<close> debug output is enabled. However, sometimes the well-known configuration option @{attribute unify_trace_failure}
  may be helpful when unification fails for large complicated terms.
\<close>
text \<open>

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.biresolution\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context option\<close>)\\
  (\<open>match\<close> : \<^ML_type>\<open>bool\<close>)\\
  (\<open>rules\<close> : \<^ML_type>\<open>(bool * thm) list\<close>)\\
  (\<open>i\<close> : \<^ML_type>\<open>int\<close>)\\
  (\<open>st\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm Seq.seq\<close>
  \end{tabular}\\
  Another basic Isabelle reasoning primitive implementing \<^emph>\<open>resolution\<close> of a proof state with a rule (actually,
  a finite sequence of alternative rules). Resolution is a special case of composition. To explain it more clearly,
  let's first introduce a special auxiliary operation called \<^emph>\<open>lifting\<close> of a theorem over a proposition. Let's assume
  we have a theorem  \<open>r\<close> of the form \<open>A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> A\<^sub>m \<Longrightarrow> C\<close> and a proposition \<open>s\<close> of the form\\
  \<open>P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> S'\<close>. Here
  the shape of the propositions is understood \<^emph>\<open>literally\<close>, i.\,e. the terms \<open>C\<close> and \<open>S'\<close> \<^emph>\<open>cannot\<close>
  themselves be meta-implications (of the form \<open>A \<Longrightarrow> B\<close>). Now, a new theorem \<open>r'\<close> is obtained from the theorem \<open>r\<close>
  by \<^emph>\<open>lifting it over\<close> the proposition \<open>s\<close> in the following two steps:
  \<^item> The schematic variables of the theorem \<open>r\<close> are renamed to necessarily differ from \<^emph>\<open>all\<close> the variables of the
    theorem \<open>s\<close>. Here there are two important details. First, such renaming of schematic variables is greatly
    facilitated by their specific representation, where each variable is supplied with an additional \<^emph>\<open>index\<close> also
    considered part of its name. So the renaming amounts to incrementing the index of every schematic variable in \<open>r\<close>
    by the value of the current maximal index of the proposition \<open>s\<close>
    (that is actually tracked for exactly this purpose).
    Second, in reality, the stored maximal index of a certified term can be \<^emph>\<open>larger\<close> than it actually is
    (without losing the uniquness after renaming). This is employed during resolution since \<open>s\<close> is usually just
    a part of a larger proposition with potentially larger maximal index.
  \<^item> The \<^emph>\<open>premises\<close> \<open>P\<^sub>1, \<dots>, P\<^sub>n\<close> are introduced as additional \<^emph>\<open>assumptions\<close> to \<^emph>\<open>every assumption\<close> of the theorem \<open>r\<close>
    with renamed variables,
    resulting in a new theorem\\
    \<open>(P\<^sub>1\<Longrightarrow>\<dots>\<Longrightarrow>P\<^sub>n\<Longrightarrow>A\<^sub>1)\<Longrightarrow>\<dots>\<Longrightarrow>(P\<^sub>1\<Longrightarrow>\<dots>\<Longrightarrow>P\<^sub>n\<Longrightarrow>A\<^sub>m)\<Longrightarrow>C\<close>\\
    called the theorem \<open>r\<close> \<^emph>\<open>lifted over\<close> the proposition \<open>s\<close>.


  Now let's consider a proof state \<open>st\<close> as usually seen in the context of theorem composition:\\
  \<open>S\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>i \<Longrightarrow> \<dots> \<Longrightarrow> S\<^sub>n \<Longrightarrow> G\<close>.\\
  Let's consider the \<open>i\<close>-th premise of the state usually called its \<open>i\<close>-th \<^emph>\<open>subgoal\<close>. We assume it to be syntactically
  of the same form as the proposition \<open>s\<close> we just contemplated above: \<open>P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> S'\<^sub>i\<close>. Now we are almost ready
  to precisely specify resolution. However, it has one specific difference from the usual composition that \<^emph>\<open>cannot\<close> be
  achieved through a call to \<^ML>\<open>Thm.bicompose\<close>. Let's pretend we have an additional flag to make \<^ML>\<open>Thm.bicompose\<close> find
  not the unifiers between \<open>C\<close> and \<open>S\<^sub>i\<close>, but between \<open>C\<close> and \<open>S'\<^sub>i\<close>. Let's also denote the result of lifting
  of a theorem \<open>r\<close> over the \<open>i\<close>-th subgoal of a proof state \<open>st\<close> as \<open>r\<^bsup>st\<^sub>i\<^esup>\<close>. Then the result of the resolution obtained
  by a call to \<^ML_text>\<open>Thm.biresolution ctxt match\<close> \<open>[\<dots>, (f\<^sub>i, r\<^sub>i), \<dots>]\<close> \<^ML_text>\<open>i st\<close> can be informally described as:\\
  \<open>\<dots>\<langle>Thm.bicompose' ctxt {flatten=true, match=match, incremented=true} (f\<^sub>j, r\<^sub>j\<^bsup>st\<^sub>i\<^esup>, m\<^sub>j) i st\<rangle>\<dots>\<close>.\\
  Here \<open>Thm.bicompose'\<close> is that modified function that looks for \<open>\<theta>\<close>s such that \<open>\<theta>C\<equiv>\<theta>S'\<^sub>i\<close>, \<open>m\<^sub>j\<close> is the number of
  assumptions of the rule \<open>r\<^sub>j\<close>, and the resulting lazy sequences of results are concatenated in order of their
  occurrence in the original list \<open>rules\<close>. Unfortunately, to avoid inevitable confusion after obtaining unexpected
  results from the vast majority of Isabelle operations, both the internal (available to the ML programmer only) and
  the surface ones (available to the user), it eventually deemed necessary to describe the Isabelle's
  resolution in \<^emph>\<open>that\<close> much detail, after failing to find a simpler and more intuitive description. The positive side
  of this is that nearly all Isabelle's proof methods and attributes, including @{attribute OF}, @{method rule},
  @{method elim}, @{method intro} and even @{method auto} are built upon this rather powerful basic mechanism and
  inherit all of its idiosyncrasies.
\<close>
text \<open>

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 RSN\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>RSN\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(r, (st, i))\<close> : \<^ML_type>\<open>thm * (int -> thm)\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Returns the unique result of the following call: \<^ML_text>\<open>Thm.biresolution NONE false [(false, r)] i st\<close>.
  Intuitively, resolves the rule \<open>r\<close> with the \<open>i\<close>-th subgoal of the state \<open>st\<close>. \<^emph>\<open>Raises\<close> an exception \<^ML_text>\<open>THM\<close> if
  the result of the resolution is either empty or not a singleton.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 RS\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>RS\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(r, st))\<close> : \<^ML_type>\<open>thm * thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Same as \<^ML_text>\<open>r RSN (1, st)\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 RLN\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>RLN\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(rs, (i, sts))\<close> : \<^ML_type>\<open>thm list * (int * thm list)\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Returns an eagerly evaluated list \<open>\<dots>\<langle>Thm.biresolution NONE false [\<dots>(false, r\<^sub>j)\<dots>] i st\<^sub>i\<rangle>\<dots>\<close>, i.\,e. concatenates
  all possible resolutions of the \<open>i\<close>-th subgoals of the states \<open>sts\<close> with every rule in the list \<open>rs\<close>. Intuitively,
  it returns the ``Cartesian'' resolution of the list of states \<open>sts\<close> with the list of rules \<open>rs\<close> ordered first
  by the state and then by the rule.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 RL\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>RL\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(rs, sts)\<close> : \<^ML_type>\<open>thm list * thm list\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Same as \<^ML_text>\<open>rs RSN (1, sts)\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 COMP\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>COMP\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(r, st)\<close> : \<^ML_type>\<open>thm * thm\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Returns the unique singleton result of\\
  \<open>Thm.bicompose NONE { flatten=true, match=false, incremented=false } (false, r, 0) 1 st\<close>.
  Raises \<^ML_text>\<open>THM\<close>, if the result is not a singleton.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 INCR_COMP\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>INCR_COMP\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(r, st)\<close> : \<^ML_type>\<open>thm * thm\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Increments indexes of schematic variables in the rule \<open>r\<close> by the maximal index of \<open>st\<close>, then returns
  \<^ML_text>\<open>r COMP st\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 COMP_INCR\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>COMP_INCR\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(r, st)\<close> : \<^ML_type>\<open>thm * thm\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Increments indexes of schematic variables in the state \<open>st\<close> by the maximal index of \<open>r\<close>, then returns\\
  \<^ML_text>\<open>r COMP st\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Drule.multi_resolve\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context option\<close>)\\
  (\<open>rs\<close> : \<^ML_type>\<open>thm list\<close>)\\
  (\<open>st\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm Seq.seq\<close>
  \end{tabular}\\
  Iteratively resolves every subgoal of the state \<open>st\<close> (\<^emph>\<open>starting from\<close> \<open>1\<close>) with each corresponding
  rule \<open>r\<^sub>i\<close> from the list \<open>rs\<close> (\<^emph>\<open>left to right\<close>, until there are no more rules to resolve)
  by calling\\ \<^ML_text>\<open>Thm.biresolution ctxt false\<close> \<open>[(false, r\<^sub>i)] i st\<^sub>i\<close>. Basically, this
  corresponds to the resolution offered by the standard Isabelle @{attribute OF} attribute (\<open>st [OF rs]\<close>). However,
  \<^ML>\<open>Drule.multi_resolve\<close> handles \<^ML_text>\<open>THM\<close> exceptions (returning an empty sequence) and supports
  multiple alternative results as if the resolution is composed by the \<open>bind\<close> operator of the Haskell's List monad.
  It should be noted, though, that for some reason the binding (and therefore enumeration of alternatives)
  starts \<^emph>\<open>from the last\<close> resolution (the last element with the last subgoal) rather than from the first.


  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 MRS\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>MRS\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(rs, st)\<close> : \<^ML_type>\<open>thm list * thm\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Returns the result of \<^ML_text>\<open>Drule.multi_resolve NONE rs st\<close>, if it is a singleton and raises \<^ML_text>\<open>THM\<close>
  otherwise.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>infix 0 OF\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>OF\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>(st, rs)\<close> : \<^ML_type>\<open>thm * thm list\<close>) :\\
  \<^ML_type>\<open>thm list\<close>
  \end{tabular}\\
  Same as \<^ML_text>\<open>st OF rs\<close>.
\<close>
text \<open>

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>zero_var_indexes\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Zeroes all indexes of schematic variables of the theorem by renaming them, if necessary. Note that renaming
  is performed \<^emph>\<open>not by\<close> adding indexes, but according to a special algorithm, which produces arguably more readable
  names such as \<open>x, xa, \<dots>, xz, xaa, \<dots>, xaz, xba, \<dots>\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>instantiate'_normalize\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>typs\<close> : \<^ML_type>\<open>ctyp option list\<close>)\\
  (\<open>terms\<close> : \<^ML_type>\<open>cterm option list\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  Instantiates similarily to \<^ML>\<open>Thm.instantiate'\<close> and then \<^emph>\<open>bet-eta normalizes\<close> the theorem \<open>thm\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.eq_thm_prop\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>thms\<close> : \<^ML_type>\<open>thm * thm\<close>) :\\
  \<^ML_type>\<open>bool\<close>
  \end{tabular}\\
  Check whether two theorems state \<^emph>\<open>alpha-convertible\<close> propositions.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Thm.abstract_rule\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>string\<close>)\\
  (\<open>t\<close> : \<^ML_type>\<open>cterm\<close>)\\
  (\<open>thm\<close> : \<^ML_type>\<open>thm\<close>) :\\
  \<^ML_type>\<open>thm\<close>
  \end{tabular}\\
  The LCF rule for lambda-abstraction over equality, a.k.a the \<^emph>\<open>abstractoin rule\<close> \<open>t \<equiv> u \<Longrightarrow> \<lambda>x. t \<equiv> \<lambda>x. u\<close>. The
  terms \<open>\<lambda>x. _\<close> are obtained by abstracting over the occurrences of \<^emph>\<open>free\<close> or \<^emph>\<open>schematic\<close> variable \<open>t\<close>
  (passed as a certified term) and renaming the resulting lambda-bound variable to \<open>x\<close>. \<open>t\<close> \<^emph>\<open>must not be free\<close> in the
  hypotheses.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Lin_Arith.simproc\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>ctxt\<close> : \<^ML_type>\<open>Proof.context\<close>)\\
  (\<open>t\<close> : \<^ML_type>\<open>cterm\<close>) :\\
  \<^ML_type>\<open>thm option\<close>
  \end{tabular}\\
  Performs linear arithmetic simplifications of the term \<open>t\<close> and returns the theorem stating \<open>t = t'\<close>, where \<open>t'\<close> is
  the simplified term. Supports all types of class \<^class>\<open>linordered_idom\<close>, including \<open>int\<close>.

  \<^bigskip>

  \marginsymbol
  \<^ML_text>\<open>val\<close> \<^ML>\<open>single\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>) :\\
  \<^ML_type>\<open>'a list\<close>&= \<^ML_text>\<open>[x]\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>curry\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a * 'b -> 'c\<close>)\\
  (\<open>a\<close> : \<^ML_type>\<open>'a\<close>)\\
  (\<open>b\<close> : \<^ML_type>\<open>'b\<close>) :\\
  \<^ML_type>\<open>'c\<close>&= \<^ML_text>\<open>f a b\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>try\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'b\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>)\\
  \<^ML_type>\<open>'b option\<close>&= \<^ML_text>\<open>SOME (f x) handle _ => NONE\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>the_default\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>d\<close> : \<^ML_type>\<open>'a\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'a option\<close>)\\
  \<^ML_type>\<open>'a\<close>&= \<^ML_text>\<open>case x of SOME x => x | NONE => d\<close>
  \end{tabular}\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>perhaps\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'a option\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>)\\
  \<^ML_type>\<open>'a\<close>&= \<^ML_text>\<open>the_default x (f x)\<close>
  \end{tabular}\\
  Some useful Isabelle/ML shortcuts.

  \<^bigskip>

  \<^ML_text>\<open>val\<close> \<^ML>\<open>perhaps_loop\<close>\\
  \tab\begin{tabular}{ll}
  (\<open>f\<close> : \<^ML_type>\<open>'a -> 'a option\<close>)\\
  (\<open>x\<close> : \<^ML_type>\<open>'a\<close>)\\
  \<^ML_type>\<open>'a option\<close>
  \end{tabular}\\
  Iteratively applies the function \<open>f\<close> to its argument until it returns \<open>NONE\<close>. Returns the unwrapped result \<open>r\<close> from
  the \<^emph>\<open>last time\<close> it returned \<open>SOME r\<close>, if any.

  \<^bigskip>

  \<^ML_text>\<open>val\<close> \<^ML>\<open>Drule.equal_elim_rule1\<close> : \<^ML_type>\<open>thm\<close>\\
  \<^ML_text>\<open>val\<close> \<^ML>\<open>Drule.equal_elim_rule2\<close> : \<^ML_type>\<open>thm\<close>\\
  The theorems\\ @{thm equal_elim_rule1} and\\ @{thm equal_elim_rule2}\\ correspondingly.
\<close>

subsection \<open>Theorems\<close>

text \<open>
\begin{tabular}{rl}
  \<open>eq_reflection\<close>:&    @{thm eq_reflection[no_vars]}\\
  \<open>someI_ex\<close>:&         @{thm someI_ex[no_vars]}\\
  \<open>HOL.nnf_simps(5)\<close>:& @{thm HOL.nnf_simps(5)[no_vars]}\\
  \<open>conj_commute\<close>:&     @{thm conj_commute[no_vars]}\\
  \<open>Diff_iff\<close>:&         @{thm Diff_iff[no_vars]}\\
  \<open>set_eq_iff\<close>:&       @{thm set_eq_iff[no_vars]}\\
  \<open>not_all\<close>:&          @{thm not_all[no_vars]}\\
  \<open>singleton_iff\<close>:&    @{thm singleton_iff[no_vars]}\\
  \<open>UnE\<close>:&              @{thm UnE[no_vars]}\\
  \<open>atomize_not\<close>:&      @{thm atomize_not[no_vars]}\\
  \<open>not_less\<close>:&         @{thm not_less[no_vars]}
\end{tabular}
\<close>

subsection \<open>Problems\<close>

text \<open>
  \<^enum> Prove the statement \<open>x \<equiv> y \<Longrightarrow> P x \<equiv> P y\<close> using the LCF approach.
  \<^enum> Implement an auxiliary function to turn HOL (object) equalities (\<open>=\<close>) into meta-equalities \<open>\<equiv>\<close> using the
    theorem \<open>eq_reflection\<close> (@{thm eq_reflection[no_vars]}) and forward reasoning.
  \<^enum> Write auxiliary functions to substitute the \<open>n\<close>-th occurrence and
    all occurrences of the LHS of an equality in a theorem. Use composition/resolution and the auxiliary
    theorem proved for problem \<open>1\<close> to perform the substitution.
  \<^enum> Given the following definition:\\
    \<^theory_text>\<open>definition "w s t \<equiv> SOME x. x \<in> s - t \<or> x \<in> t - s"\<close>\\
    and using the theorems and functions obtained earlier, prove the following statement:\\
    \<open>s \<noteq> t \<Longrightarrow> w s t \<in> s - t \<or> w s t \<in> t - s\<close>.
  \<^enum> Prove the following statement: \<open>x \<in> {1} \<union> {2} \<Longrightarrow> x \<le> 2\<close> using resolution as well as basic LCF inference.
\<close>

definition "w s t \<equiv> SOME x. x \<in> s - t \<or> x \<in> t - s"

subsection \<open>Solutions\<close>

subsubsection \<open>Problem 1\<close>

ML \<open>
  val cong =
    let
      val asm = \<^cprop>\<open>x :: 'a \<equiv> y\<close>
    in
      \<^cterm>\<open>P :: 'a \<Rightarrow> prop\<close> |>
      Thm.reflexive |>
      rpair (Thm.assume asm) |->
      Thm.combination |>
      Thm.implies_intr asm |>
      Drule.generalize (["'a"], ["P", "x", "y"])
    end
\<close>

subsubsection \<open>Problem 2\<close>

ML \<open>
  val meta_eq = try (fn r => r RS @{thm eq_reflection}) |> perhaps
\<close>

subsubsection \<open>Problem 3\<close>

ML \<open>
local
   \<comment> \<open>Substitute \<open>n\<close>-th occurrence of \<open>cE\<close>'s LHS in \<open>thm\<close>\<close>
  fun subst' ctxt cE n thm =
    let
      fun diff thm' = Thm.eq_thm_prop (thm, thm') |> not
    in
      cE |>
      meta_eq |>
      single |>
      curry op OF cong |>
      single |>
      curry op OF Drule.equal_elim_rule1 |>
      (fn thm' => Drule.multi_resolve (SOME ctxt) [thm] thm') |>
      Seq.filter diff |>
      Seq.chop n |>
      fst |>
      try List.last
    end
in
  fun subst ctxt cE n = subst' ctxt cE n #> the
  fun subst_all ctxt cE = perhaps_loop (subst' ctxt cE 1) #> the
end
\<close>

subsubsection \<open>Problem 4\<close>

experiment begin
lemma set_neqD:
  "s \<noteq> t \<Longrightarrow> w s t \<in> s \<and> w s t \<notin> t \<or> w s t \<notin> s \<and> w s t \<in> t"
proof-
  assume "s \<noteq> t"
  then obtain x where "(x \<in> s) \<noteq> (x \<in> t)" unfolding set_eq_iff not_all by (elim exE)
  hence "x \<in> s \<and> x \<notin> t \<or> x \<notin> s \<and> x \<in> t" unfolding HOL.nnf_simps(5) .
  hence "x \<in> s \<and> x \<notin> t \<or> x \<in> t \<and> x \<notin> s" by (subst (asm) (2) conj_commute)
  thus ?thesis unfolding w_def Diff_iff
    by (subst (8) conj_commute) (erule someI[where P="\<lambda> x.  x \<in> s \<and> x \<notin> t \<or> x \<in> t \<and> x \<notin> s"])
qed
end

ML \<open>
  val prove_set_neqD =
    let
      val asm = \<^cprop>\<open>(s :: 'a set) \<noteq> t\<close>
      val someI_ex =
        @{thm someI_ex} |>
        Drule.instantiate'_normalize [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>\<lambda> x. x \<in> s \<and> x \<notin> t \<or> x \<in> t \<and> x \<notin> s\<close>]
      val nnf_simp =
        @{thm HOL.nnf_simps(5)} |>
        Drule.instantiate'_normalize [] [SOME \<^cterm>\<open>P x :: bool\<close>, SOME \<^cterm>\<open>Q x :: bool\<close>] |>
        Drule.generalize ([], ["P", "Q"]) |>
        meta_eq |>
        Thm.abstract_rule "x" \<^cterm>\<open>x\<close>
      val conj_commute =
        @{thm conj_commute} |>
        Drule.instantiate'_normalize [] [SOME \<^cterm>\<open>x \<notin> s\<close>, SOME \<^cterm>\<open>x \<in> t\<close>] |>
        meta_eq |>
        Thm.abstract_rule "x" \<^cterm>\<open>x\<close>
      val diff =
        @{thm Diff_iff} |>
        Drule.instantiate'_normalize [SOME \<^ctyp>\<open>'a\<close>] [SOME \<^cterm>\<open>x :: 'a\<close>] |>
        meta_eq |>
        Thm.symmetric |>
        Thm.abstract_rule "x" \<^cterm>\<open>x\<close>
    in
      Thm.assume asm |>
      subst \<^context> @{thm set_eq_iff} 1 |>
      subst \<^context> @{thm not_all} 1 |>
      subst \<^context> nnf_simp 1 |>
      subst \<^context> conj_commute  1 |>
      Thm.implies_elim someI_ex |>
      subst_all \<^context> diff |>
      subst_all \<^context> (@{thm w_def} |> Thm.symmetric) |>
      Thm.implies_intr asm |>
      Drule.generalize (["'a"], ["s", "t"]) |>
      Drule.zero_var_indexes |>
      pair \<^binding>\<open>set_neqD\<close> |>
      Global_Theory.store_thm #>
      snd
    end
\<close>

setup \<open>prove_set_neqD\<close>

thm set_neqD

subsubsection \<open>Problem 5\<close>

ML \<open>
  val prove_sample1 =
    let
      val in_Un = \<^cprop>\<open>x \<in> {1} \<union> {2 :: int}\<close>
      val gt2 = \<^cprop>\<open>(2 :: int) < x\<close>
      val in_1 = \<^cprop>\<open>x \<in> {1 :: int}\<close>
      val in_2 = \<^cprop>\<open>x \<in> {2 :: int}\<close>
      val False1 =
        Thm.assume in_1 |>
        subst_all \<^context> @{thm singleton_iff} |>
        rpair (Thm.assume gt2) |->
        subst_all \<^context> |>
        pair (Lin_Arith.simproc \<^context> \<^cterm>\<open>2 < (1 :: int)\<close> |> the) |->
        subst_all \<^context> |>
        Thm.implies_intr in_1
      val False2 =
        Thm.assume in_2 |>
        subst_all \<^context> @{thm singleton_iff} |>
        rpair (Thm.assume gt2) |->
        subst_all \<^context> |>
        pair (Lin_Arith.simproc \<^context> \<^cterm>\<open>2 < (2 :: int)\<close> |> the) |->
        subst_all \<^context> |>
        Thm.implies_intr in_2
      val thm =
        (Thm.assume in_Un RS @{thm UnE}) |>
        curry op COMP False1 |>
        curry op COMP False2 |>
        Thm.implies_intr gt2 |>
        Thm.equal_elim (@{thm atomize_not} |>  Drule.instantiate'_normalize [] [SOME \<^cterm>\<open>(2 :: int) < x\<close>]) |>
        Thm.implies_intr in_Un |>
        subst_all \<^context> @{thm not_less} |>
        Drule.generalize ([], ["x"]) |>
        Drule.zero_var_indexes
    in
      thm |>
      pair \<^binding>\<open>sample1\<close> |>
      Global_Theory.store_thm #>
      snd
    end
\<close>

setup \<open>prove_sample1\<close>

thm sample1
end