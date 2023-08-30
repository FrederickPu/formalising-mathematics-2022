import data.nat.factorial.basic
import data.finset.basic
import algebra.big_operators
import tactic

open_locale big_operators
open nat


lemma mul_tb (a b : ℚ) (hb : b ≠ 0): a = a * (b / b) := begin
rw div_self,
simp,
exact hb,
end

lemma frac_mul {a b c d: ℚ} : (a/b)*(c/d)=(a*c)/(b*d):= begin
field_simp,
end

lemma mul_frac {a b c : ℚ} : a*b/c = (a*b)/c := begin
field_simp,
end

example (n : ℕ) : n ≠ 0 → (n : ℚ) ≠ 0 := begin
exact cast_ne_zero.mpr,
end
theorem frac_eq {a b c d : ℚ} (hb : b ≠ 0) (hd : d ≠ 0) : a*d=b*c → a/b = c/d := begin
field_simp,
intro h,
rw mul_comm c b,
exact h,
end

-- we modify formula b/c range is 0 indexed in lean
theorem odd_product_formula (n : ℕ) :
  ∏ i in finset.range n, ((2 * (i+1) - 1):ℚ)= ((2 * n).factorial:ℚ) / (n.factorial * 2^n :ℚ) :=
begin
  induction n with k hk,
  { -- Base case: n = 0
    simp [factorial, finset.prod_range_zero] },
  { -- Inductive case: n = k + 1
    have : 2 * k.succ = (2*k).succ.succ,
      have l : ∀ {x:ℕ}, x.succ = x+ 1 := congr_fun rfl,
      repeat {rw l},
      ring,
    rw this,
    simp only [finset.prod_range_succ, factorial_succ, pow_succ], -- ∏ product definition
    rw hk, -- use induction hypothesis
    field_simp, apply frac_eq _ _, -- clear denominators
    ring,

    -- extra-stuff prove denominators are nonzero (b/c frac_eq)
    apply mul_ne_zero,
    exact cast_ne_zero.mpr (factorial_ne_zero k),
    suffices : (2:ℚ) ≠ 0,
      exact pow_ne_zero k this,
    norm_num,

    apply mul_ne_zero,
    {
      apply mul_ne_zero,

      exact cast_add_one_ne_zero k,
      exact cast_ne_zero.mpr (factorial_ne_zero k),
    },
    rw ← pow_succ,
    norm_num,
  }
end

