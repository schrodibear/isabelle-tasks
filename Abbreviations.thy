theory Abbreviations
  imports Main
begin

lemma "x \<noteq> y \<Longrightarrow> y \<noteq> x" using [[show_abbrevs=false]] not_sym .

lemma "range ((*) 0) = {0 :: int}" using [[show_abbrevs=false]] by simp

lemma "(n :: nat) \<ge> 0" ..

abbreviation sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "sym_diff A B \<equiv> ((A - B) \<union> (B-A))"

lemma "sym_diff A B = {} \<Longrightarrow> A = B" using [[show_abbrevs=false]] by auto

lemma "map2 (+) [1,2] [3,4] = [4, 6]" using [[show_abbrevs=false]]
  unfolding zip.simps list.case list.map prod.case by simp
lemma "map2 (+) [1,2] [3,4] = [4, 6]" by simp

experiment begin
abbreviation "U F x \<equiv> F (F x)"
term "U U g x"
term "U g (U g x)"
term "g (g (g (g x)))"
term "x + 1 + 1 + 1 + 1"
term "U U (\<lambda> x. x + 1) x"
end

experiment begin
abbreviation "U F x \<equiv> F x x"
term "U F x"
term "x + x"
term "(x + x) + (x + x)"
term "U (\<lambda> x y. x + y + 1) x"
end

experiment begin
abbreviation "U F x \<equiv> F 0"
term "U (\<lambda> x. x + x) 0"
term "0 + 0"
end

end