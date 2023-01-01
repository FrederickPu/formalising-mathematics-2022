import tactic
import set_theory.cardinal

open_locale cardinal

#check equiv

-- same proof as previously but using equivalence
-- notice proof is longer, but less lemmas and more straightforward
lemma l1 : fin 6 ≃ subtype (λ x : fin 16, ∃ k : ℕ, 3 * k = x) :=
{
  to_fun := begin
    intro x, cases x,
    have : 3 * x_val < 16, linarith,
    exact ⟨⟨3*x_val, this⟩, by use x_val, rfl⟩,
  end,
  inv_fun := begin
    intro x', cases x' with x x'prop,
    cases x,
    have h := Exists.some_spec x'prop,
    simp at h,

    have : x_val/3 < 6,
    {
      rw ← h at *,
      rw nat.mul_div_right (Exists.some _) nat.succ_pos',
      linarith,
    },

    exact ⟨x_val / 3, this⟩,
  end,
  left_inv := begin
    intro x,
    simp,
    cases x,
    simp only [nat.succ_pos', nat.mul_div_right],
  end,
  right_inv := begin
    intro x,
    -- keep doing cases until lean finds something it can simplify
    cases x, cases x_val,
    simp,
    cases x_property with k kh,
    simp at kh,
    rw ← kh,
    simp,
  end
}

example : # (fin 6) = # (subtype (λ x : fin 16, ∃ k : ℕ, 3 * k = x)) :=
begin
rw cardinal.mk_congr,
exact l1,
end

lemma nat_quot (n m : ℕ) (hn : n > 0) (hm : m > 0) : fin (n+1) ≃ subtype (λ x : fin (n*m+1), ∃ k : ℕ, m * k = x) :=
{
  to_fun := begin
    intro x, cases x,
    have := nat.le_of_lt_succ x_property,
    have : x_val*m ≤ n*m, exact mul_le_mul_right' this m,
    rw nat.mul_comm at this,

    exact ⟨⟨m*x_val, nat.lt_succ_of_le this⟩, by use x_val, rfl⟩,
  end,
  inv_fun := begin
    intro x', cases x' with x x'prop,
    cases x,
    have h := Exists.some_spec x'prop,
    simp at h,

    have p := nat.le_of_lt_succ x_property,

    have : x_val/m ≤ n,
    {
      rw ← h at *,
      rw nat.mul_div_right (Exists.some _) hm,
      rw mul_comm at p,
      exact (mul_le_mul_right hm).mp p,
    },

    exact ⟨x_val / m, nat.lt_succ_of_le this⟩,
  end,
  left_inv := begin
    intro x,
    simp,
    cases x,
    simp only [subtype.mk_eq_mk],
    exact nat.mul_div_right x_val hm,
  end,
  right_inv := begin
    intro x,
    -- keep doing cases until lean finds something it can simplify
    cases x, cases x_val,
    simp,
    cases x_property with k kh,
    simp at kh,
    rw ← kh,
    rw nat.mul_div_right k hm,
  end
}

-- when you declare function as an intermediate variable using `have`
-- notation, lean does not know any of its internal contents
-- however, when you describe a function directly as a definition
-- (like u would in a structure declaration) it will remember

-- def f : ℕ → ℕ :=
-- begin
-- intro x,
-- exact x + 2,
-- end

-- example : false :=
-- begin
-- have g : ℕ → ℕ,
--   {intro x,
--   exact x + 2,},

-- have : ∀ x, f x = x + 2,
-- rw f, -- can rewrite f because declared with :=
-- have : ∀ x, g x = x + 2,
-- rw g, -- can't rw g b/c it's declared with `have`
-- end

