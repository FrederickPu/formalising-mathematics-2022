import leetcode.field_simp_better

import data.real.basic

import algebra.big_operators.basic
import data.nat.factorial.basic

open_locale big_operators
open nat

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
    field_simp,
    assert_denoms_nonzero,
    field_simp,
    ring,

    -- extra-stuff prove denominators are nonzero (b/c frac_eq)
    apply mul_ne_zero,
    apply mul_ne_zero,
    exact cast_add_one_ne_zero k,
    exact cast_ne_zero.mpr (factorial_ne_zero k),

    rw ← pow_succ,
    norm_num,

    apply mul_ne_zero,
    exact cast_ne_zero.mpr (factorial_ne_zero k),
    suffices : (2 : ℚ) ≠ 0,
      exact pow_ne_zero _ this,
    exact two_ne_zero,
  }
end

#check ordered_semiring
structure pos_ (α : Type*) [ordered_cancel_add_comm_monoid α] :=
(a : α)
(isPos : a > 0)

notation `ℕ⁺` := pos_ nat
notation `ℤ⁺` := pos_ int
notation `ℚ⁺` := pos_ rat
notation `ℝ⁺` := pos_ real

#check (⟨1, by linarith⟩ : ℕ⁺)

