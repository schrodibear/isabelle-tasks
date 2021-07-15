theory From_Inferences_To_Isar
  imports Pure
begin

text \<open>Prove that \<^prop>\<open>(PROP A &&& PROP B &&& PROP C) \<equiv> (PROP C &&& PROP B &&& PROP A)\<close>\<close>

ML \<open>
local
  fun swap_conj AB =
    let
      val (A, B) = Conjunction.elim AB
    in
      Conjunction.intr B A
    end
  fun conj_comm P Q =
    let
      val PQ = Conjunction.mk_conjunction (P, Q)
      val QP = Conjunction.mk_conjunction (Q, P)
    in
      Thm.equal_intr
        (Thm.assume PQ |> swap_conj |> Thm.implies_intr PQ)
        (Thm.assume QP |> swap_conj |> Thm.implies_intr QP)
    end
  fun shift_conj_left ABC =
    let
      val (A, BC) = Conjunction.elim ABC
      val (B, C) = Conjunction.elim BC
    in
      Conjunction.intr (Conjunction.intr A B) C
    end
  fun shift_conj_right ABC =
    let
      val (AB, C) = Conjunction.elim ABC
      val (A, B) = Conjunction.elim AB
    in
      Conjunction.intr A (Conjunction.intr B C)
    end
  fun conj_assoc P Q R =
    let
      open Conjunction
      val PQR1 = mk_conjunction (P, mk_conjunction (Q, R))
      val PQR2 = mk_conjunction (mk_conjunction (P, Q), R)
    in
      Thm.equal_intr
        (Thm.assume PQR1 |> shift_conj_left |> Thm.implies_intr PQR1)
        (Thm.assume PQR2 |> shift_conj_right |> Thm.implies_intr PQR2)
    end
in
  val fact =
    Thm.reflexive \<^cterm>\<open>PROP A &&& PROP B &&& PROP C\<close>
    |> rpair (conj_assoc \<^cprop>\<open>PROP A\<close> \<^cprop>\<open>PROP B\<close> \<^cprop>\<open>PROP C\<close>)
    |-> Thm.transitive
    |> rpair (Conjunction.cong (conj_comm \<^cprop>\<open>PROP A\<close> \<^cprop>\<open>PROP B\<close>) (Thm.reflexive \<^cprop>\<open>PROP C\<close>))
    |-> Thm.transitive
    |> rpair (conj_comm \<^cprop>\<open>PROP B &&& PROP A\<close> \<^cprop>\<open>PROP C\<close>)
    |-> Thm.transitive
  \<comment> \<open>For later use\<close>
  val conj_comm = conj_comm \<^cprop>\<open>PROP A\<close> \<^cprop>\<open>PROP B\<close> |> Drule.export_without_context
  val conj_assoc = conj_assoc \<^cprop>\<open>PROP A\<close> \<^cprop>\<open>PROP B\<close> \<^cprop>\<open>PROP C\<close> |> Drule.export_without_context
end
\<close>

text \<open>
  Inconvenient, all intermediate results are expressed as rules, i.e. bare ML functions. This way proving boils
  down to mere programming without providing proper tools for incrementality of reasoning: the functions can fail
  at any point, no reliable abstractions provided. Functions can't be reliably presented, until fully applied.
  But there's a well-known tool for reliable intermediate abstractions already widely used in mathematics: theorems
  and lemmas. So let's use intermediate lemmas/theorems instead\<dots>\<close>

ML \<open>
  val cong =
    Conjunction.cong (Thm.assume \<^cprop>\<open>PROP A \<equiv> PROP B\<close>) (Thm.assume \<^cprop>\<open>PROP C \<equiv> PROP D\<close>)
    |> Thm.implies_intr \<^cprop>\<open>PROP C \<equiv> PROP D\<close> |> Thm.implies_intr \<^cprop>\<open>PROP A \<equiv> PROP B\<close>
    |> Drule.export_without_context

  fun inst thm tys vars = Drule.instantiate'_normalize (map SOME tys) (map SOME vars) thm
  val imps = List.foldl (uncurry Thm.implies_elim o swap)

  val fact =
    imps
     (inst @{thm transitive} [\<^ctyp>\<open>prop\<close>]
       [\<^cprop>\<open>PROP A &&& PROP B &&& PROP C\<close>,
        \<^cprop>\<open>(PROP A &&& PROP B) &&& PROP C\<close>,
        \<^cprop>\<open>PROP C &&& PROP B &&& PROP A\<close>])
     [inst conj_assoc [] [\<^cprop>\<open>PROP A\<close>, \<^cprop>\<open>PROP B\<close>, \<^cprop>\<open>PROP C\<close>],
      imps
        (inst @{thm transitive} [\<^ctyp>\<open>prop\<close>]
          [\<^cprop>\<open>(PROP A &&& PROP B) &&& PROP C\<close>,
           \<^cprop>\<open>(PROP B &&& PROP A) &&& PROP C\<close>,
           \<^cprop>\<open>PROP C &&& PROP B &&& PROP A\<close>])
        [imps
          (inst cong [] [\<^cprop>\<open>PROP A &&& PROP B\<close>, \<^cprop>\<open>PROP B &&& PROP A\<close>, \<^cprop>\<open>PROP C\<close>, \<^cprop>\<open>PROP C\<close>])
          [inst conj_comm [] [\<^cprop>\<open>PROP A\<close>, \<^cprop>\<open>PROP B\<close>],
           inst @{thm "reflexive"} [\<^ctyp>\<open>prop\<close>] [\<^cprop>\<open>PROP C\<close>]],
         inst conj_comm [] [\<^cprop>\<open>PROP B &&& PROP A\<close>, \<^cprop>\<open>PROP C\<close>]]]
\<close>

text \<open>Modular, reliable, regular, well-structured\<dots> But too many noisy instantiations, can't be they automated?\<close>

ML \<open>
  Thm.combination (Thm.reflexive \<^cterm>\<open>P :: 'a \<Rightarrow> prop\<close>) (Thm.assume \<^cprop>\<open>x \<equiv> y\<close>)
  |> Thm.implies_intr \<^cprop>\<open>x \<equiv> y\<close> |> Drule.store_standard_thm \<^binding>\<open>substitutivity\<close>
\<close>

experiment begin

thm asm_rl[where psi="PROP B &&& PROP A \<Longrightarrow> PROP A &&& PROP B" for A B, OF conjunctionI[OF conjunctionD2 conjunctionD1]]

lemma conjunction_comm: "(PROP A &&& PROP B) \<equiv> (PROP B &&& PROP A)"
  using equal_intr_rule[OF conjunctionI[OF conjunctionD2 conjunctionD1] conjunctionI[OF conjunctionD2 conjunctionD1]] .

lemmas D1 = conjunctionD1
lemmas D2 = conjunctionD2
lemmas I = conjunctionI

lemma conjunction_assoc: "(PROP A &&& PROP B &&& PROP C) \<equiv> ((PROP A &&& PROP B) &&& PROP C)"
  using equal_intr_rule[OF I[OF I[OF D1 D2[THEN D1]] D2[THEN D2]] I[OF D1[THEN D1] I[OF D1[THEN D2] D2]]] .

lemma subst_left: "\<lbrakk>x \<equiv> y; P y \<equiv> Q\<rbrakk> \<Longrightarrow> PROP P x \<equiv> Q" using equal_elim_rule2[OF substitutivity] .

lemma "(PROP A &&& PROP B &&& PROP C) \<equiv> (PROP C &&& PROP B &&& PROP A)"
  using subst_left[OF conjunction_assoc subst_left[OF conjunction_comm, THEN subst_left[OF conjunction_comm]]] .

end

text \<open>
  Very nice and concise proofs! But really hard to construct, seems like we need a way to construct them
  \<open>in reverse\<close>: \<^emph>\<open>backwardly\<close>!\<close>

experiment begin

lemma conjunction_comm: "(PROP A &&& PROP B) \<equiv> (PROP B &&& PROP A)"
  by (rule equal_intr_rule; (rule conjunctionI, erule conjunctionD2, erule conjunctionD1))

lemma conjunction_assoc: "(PROP A &&& PROP B &&& PROP C) \<equiv> ((PROP A &&& PROP B) &&& PROP C)"
  apply (rule equal_intr_rule; rule conjunctionI)
  subgoal by (rule conjunctionI) (erule conjunctionD1, drule conjunctionD2, erule conjunctionD1)
  subgoal by (drule conjunctionD2) (erule conjunctionD2)
  subgoal by (drule conjunctionD1) (erule conjunctionD1)
  subgoal by (rule conjunctionI) (drule conjunctionD1, (erule conjunctionD2)+)
  done

lemma subst_left: "\<lbrakk>x \<equiv> y; P y \<equiv> Q\<rbrakk> \<Longrightarrow> PROP P x \<equiv> Q" by (rule equal_elim_rule2) (rule substitutivity)

lemma "(PROP A &&& PROP B &&& PROP C) \<equiv> (PROP C &&& PROP B &&& PROP A)" by
    (rule subst_left[OF conjunction_assoc], rule subst_left[OF  conjunction_comm])
    (rule subst_left[OF conjunction_comm])

end

text \<open>
  Finally, proofs made feasible! But readability and maintainability is poor, also the high-level structure and
  the underlying mathematical insight are practically imperceptible.
  Need structured, declarative, intelligible proofs\<dots>\<close>

experiment begin

lemma conjunction_comm: "(PROP A &&& PROP B) \<equiv> (PROP B &&& PROP A)"
proof
  assume "A&B": "PROP A &&& PROP B"
  show "PROP B &&& PROP A" proof-
    from "A&B" show "PROP B" by (rule conjunctionD2)
    from "A&B" show "PROP A" by (rule conjunctionD1)
  qed
next
  assume "B&A": "PROP B &&& PROP A"
  show "PROP A &&& PROP B" proof-
    from "B&A" show "PROP A" by (rule conjunctionD2)
    from "B&A" show "PROP B" by (rule conjunctionD1)
  qed
qed

lemma conjunction_assoc: "(PROP A &&& PROP B &&& PROP C) \<equiv> ((PROP A &&& PROP B) &&& PROP C)"
proof
  show "(PROP A &&& PROP B) &&& PROP C" if "PROP A &&& PROP B &&& PROP C" proof-
    from that show "PROP A" by (rule conjunctionD1)
    from that[THEN conjunctionD2] show "PROP B" "PROP C" by - (erule conjunctionD1 conjunctionD2)+
  qed
  show "PROP A &&& PROP B &&& PROP C" if "(PROP A &&& PROP B) &&& PROP C" proof-
    from that[THEN conjunctionD1] show "PROP A" "PROP B" by - (erule conjunctionD1 conjunctionD2)+
    from that show "PROP C" by (rule conjunctionD2)
  qed
qed

lemma subst_left: "\<lbrakk>x \<equiv> y; P y \<equiv> Q\<rbrakk> \<Longrightarrow> PROP P x \<equiv> Q" by (rule equal_elim_rule2) (rule substitutivity)

lemma "(PROP A &&& PROP B &&& PROP C) \<equiv> (PROP C &&& PROP B &&& PROP A)"
proof-
  have "(PROP A &&& PROP B &&& PROP C) \<equiv> ((PROP A &&& PROP B) &&& PROP C)" by (rule subst_left[OF conjunction_assoc])
  also have "\<dots> \<equiv> ((PROP B &&& PROP A) &&& PROP C)" by (rule subst_left[OF conjunction_comm])
  also have "\<dots> \<equiv> (PROP C &&& PROP B &&& PROP A)" by (rule subst_left[OF conjunction_comm])
  finally show "(PROP A &&& PROP B &&& PROP C) \<equiv> (PROP C &&& PROP B &&& PROP A)" .
qed

end

end