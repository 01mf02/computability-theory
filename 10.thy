theory 10
imports Main
begin

fun h :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "h 0       x = x + 1"
| "h (Suc n) x = (h n ^^ x) x"

lemma h0_compow: "(h 0 ^^ n) x = n + x"
by (induct n, auto)

lemma h1: "h 1 x = 2 * x"
by (auto simp add: h0_compow)

lemma h1_compow: "(h 1 ^^ n) x = x * 2^n"
by (induct n, auto simp add: h0_compow)

theorem h2: "h 2 x = x * 2^x"
using h1_compow h.simps(2)[of 1] unfolding Suc_1 by auto


lemma hn1: "h n 1 = 2"
by (induct n, auto)

theorem h_monotonic_second: "x \<ge> y \<Longrightarrow> h n x \<ge> h n y"
sorry

lemma h_output_geq_input: "h n x \<ge> x"
sorry

lemma "(h n ^^ i) x \<ge> x"
proof (induct i)
  case (Suc i) thus ?case using h_output_geq_input[of x n]
                                h_monotonic_second[of x "(h n ^^ i) x" n] by auto
qed (simp)

lemma h_monotonic_first_suc: "h (Suc n) (Suc x) \<ge> h n (Suc x)"
proof (induct n arbitrary: x)
  case 0
    have "h 0 (Suc x) \<le> h 1 (Suc x)" unfolding h1 by auto
    then show ?case by simp
next
  case (Suc n) then show ?case sorry
qed

theorem h_monotonic_first:
  assumes "n \<ge> m"
  shows "h n (Suc x) \<ge> h m (Suc x)" using assms
proof (induct n arbitrary: m)
  case (Suc n)
    then show ?case
    proof (cases "m \<le> n")
      case False
        then have "m = Suc n" using Suc.prems by arith
        thus ?thesis using Suc(1) by auto
    next
      case True
        show ?thesis using Suc.hyps[OF True] using h_monotonic_first_suc[of n x] by auto
    qed
qed (auto)

end
