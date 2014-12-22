theory 10
imports Main
begin

(* iterate f n x calculates f\<^sup>n(x), that is, f applied n times to x *)
(* "iterate f n x" applies f n times to x *)
fun iterate :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "iterate f 0       x = x"
| "iterate f (Suc n) x = f (iterate f n x)"

fun h :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "h 0       x = x + 1"
| "h (Suc n) x = iterate (h n) x x"

lemma h0_iterate: "iterate (h 0) n x = n + x"
proof (induct n)
  case 0 show ?case by auto
  case (Suc n) then show ?case by auto
qed

lemma h1: "h 1 x = 2 * x"
by (auto simp add: h0_iterate)

lemma h1_iterate: "iterate (h 1) n x = x * 2^n"
by (induct n, auto simp add: h0_iterate)

theorem h2: "h 2 x = x * 2^x"
using h1_iterate h.simps(2)[of 1] unfolding Suc_1 by auto


lemma hn1: "h n 1 = 2"
by (induct n, auto)

theorem h_monotonic_second: "x \<ge> y \<Longrightarrow> h n x \<ge> h n y"
sorry

lemma h_output_geq_input: "h n x \<ge> x"
sorry


lemma "iterate (h n) i x \<ge> x"
proof (induct i)
  case 0 show ?case by simp
  case (Suc i) thus ?case using h_output_geq_input[of x n]
                                h_monotonic_second[of x "iterate (h n) i x" n] by auto
qed

theorem h_monotonic_first:
  assumes "n \<ge> m"
  shows "h n (Suc x) \<ge> h m (Suc x)" using assms
proof (induct n arbitrary: m)
  case 0 then show ?case by auto
  case (Suc n)
    fix n m m'
    assume A1: "m' \<le> n \<Longrightarrow> h m' (Suc x) \<le> h n (Suc x)"
    assume A2: "m \<le> Suc n"
oops

(*theorem h_monotonic_first: "n \<ge> m \<Longrightarrow> h n (Suc x) \<ge> h m (Suc x)"
proof (induct x)
  case 0 show ?case using hn1 by auto
  case (Suc x)
    then have IH1: "h m (Suc x) \<le> h n (Suc x)" by simp
    show ?case using Suc.prems proof (induct n)
      print_cases
      case 0 then show ?case by auto
      case (Suc n) 
oops*)

end
