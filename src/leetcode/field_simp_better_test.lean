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

#check (⟨1, _⟩: ℕ⁺)

structure rat':=
(val : ℚ)
(ne_zero : val ≠ 0)

structure nat':=
(val : ℕ)
(ne_zero : val ≠ 0)

notation `ℕ*` := nat'
notation `ℚ*` := rat'

def nat.factorial' : ℕ → ℕ* :=
 λ n, ⟨n.factorial, factorial_ne_zero n⟩
protected def nat'.add : ℕ* → ℕ* → ℕ* := 
  λ ⟨a, ha⟩, λ ⟨b, hb⟩, ⟨a+b, by {
    have := pos_iff_ne_zero.mpr ha,
    have := pos_iff_ne_zero.mpr hb,
    linarith,
  }⟩ 

def nat'.to_rat' : ℕ* → ℚ* :=
 λ ⟨n, hn⟩, ⟨(n : ℚ), cast_ne_zero.mpr hn⟩ 
def nat'.to_nat : ℕ* → ℕ :=
 λ ⟨n, hn⟩, n

@[reducible]
def rat'.mul : ℚ* → ℚ* → ℚ* := 
  λ ⟨a, ha⟩, λ ⟨b, hb⟩, ⟨a*b, mul_ne_zero ha hb⟩
@[reducible]
def rat'.pow : ℚ* → ℕ → ℚ* :=
  λ ⟨a, ha⟩, λ n, ⟨a^n, pow_ne_zero n ha⟩ 

instance : has_coe ℕ* ℚ* :=
⟨nat'.to_rat'⟩
instance : has_coe ℕ* ℕ :=
⟨nat'.to_nat⟩
instance : has_add ℕ* :=
⟨nat'.add⟩
instance : has_mul ℚ* :=
⟨rat'.mul⟩
instance : has_pow ℚ* ℕ :=
⟨rat'.pow⟩

@[simp]
theorem nat'.add_nat_cast (a b : ℕ*) : (a+b).val = a.val + b.val := begin
cases a with a ha,
cases b with b hb,
refl,
end

@[simp]
theorem rat'.mul_rat_cast (a b : ℚ*) : (a*b).val = a.val*b.val := begin
cases a with a ha,
cases b with b hb,
refl,
end

@[simp]
theorem rat'.pow_rat_cast (a : ℚ*) (n : ℕ) : (a^n).val = a.val^n := begin
cases a with a ha,
refl,
end

@[simp]
theorem nat'.cast_rat'_rat_cast (n : ℕ*) : (n : ℚ*).val = (n.val : ℚ) := begin
cases n with n hn,
refl,
end
-- proof redo using our nonzero machinery
theorem odd_product_formula' (n : ℕ) :
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
    let why := ((⟨k + 1, by linarith⟩ : ℕ*) : ℚ*) * (k.factorial') * ((⟨2, by linarith⟩: ℚ*)*(⟨2, by linarith⟩: ℚ*)^k),
    have := why.ne_zero,
    simp only [rat'.mul_rat_cast, nat'.cast_rat'_rat_cast, rat'.pow_rat_cast] at this,
    exact this,

    let why := ((k.factorial'):ℚ*) * (⟨2, by linarith⟩: ℚ*)^k,
    have := why.ne_zero,
    simp only [rat'.mul_rat_cast, nat'.cast_rat'_rat_cast, rat'.pow_rat_cast] at this,
    exact this,
  }
end