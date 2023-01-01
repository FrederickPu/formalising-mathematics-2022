import data.real.basic
import analysis.mean_inequalities_pow -- gives instance of: `has_pow ℝ ℝ`
import tactic

noncomputable theory

example (a b c : ℝ) (n : ℕ) : (a*b*c)^n = a^n*b^n*c^n :=
begin
simp [mul_pow],
end

lemma rpow_distrib3 {a b c : ℝ} {n : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
: (a*b*c)^n = a^n*b^n*c^n :=
begin
rw real.mul_rpow,
rw real.mul_rpow,

exact ha, exact hb, 
exact mul_nonneg ha hb,
exact hc,
end

example (a b c d: ℝ) (n : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0)
: (a*b*c*d)^n = a^n*b^n*c^n*d^n :=
begin
rw real.mul_rpow,
rw rpow_distrib3 ha hb hc,
exact mul_nonneg (mul_nonneg ha hb) hc,
exact hd,
end

meta def bruhlol : tactic unit :=
do { 
  `[intro k],
  `[norm_num [range]],
  `[intro p],
  `[repeat {any_goals {cases p}}],
  `[skip]
} <|> tactic.fail "failed to simplify range expression"