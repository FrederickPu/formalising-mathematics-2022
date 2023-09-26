import tactic -- imports all the Lean tactics
import data.real.sqrt -- the reals

-- Q1 a) TRUE
example : {xy : ℝ × ℝ | xy.fst - 1 = 0} ⊆ {xy : ℝ × ℝ | xy.fst * (xy.fst - 1) = 0}:= begin
intro x,
simp only [set.mem_set_of_eq],
intro h,
rw h,
ring,
end

-- Q1 b) FALSE
example : ¬ ({x : ℝ | ∃ y : ℤ , x = y}.prod (set.univ) ⊆ set.univ.prod ({x : ℝ | ∃ y : ℤ , x = y})) := begin
intro  h,
simp only [set.subset_def] at h,
specialize h (⟨(1:ℝ), (1/2:ℝ)⟩),
simp at h,
specialize h 1,
simp at h,

cases h with y hy,
have l : 0 < (2⁻¹:ℝ),
simp,
have r : (2⁻¹ : ℝ) < 1,
norm_num,

rw hy at l, rw hy at r,
simp at l,
rw ← int.cast_one at r,
have : y < 1 := int.cast_lt.mp r,

linarith,
end

-- Q2 a)
universes u v
example (A : Type u) (B : Type v) (f : A → B) (C D : set A) : f '' (C ∩ D) ⊆ (f '' C) ∩ (f '' D) := begin
intros a ha,
simp at ha,
split,
{
cases ha with x hx,
use x, tauto,
},
{
cases ha with x hx,
use x, tauto,
},
end

-- Q2 b)
example : ∃ (f : ℝ → ℝ), ∃ (C D : set ℝ), f '' (C ∩ D) ≠ (f '' C) ∩ (f '' D) := begin
use (λ x : ℝ, x^2),
use {(1:ℝ)}, use {(-1:ℝ)},
simp,
have : (1:ℝ)  ≠ -1, linarith,
have : {(1 : ℝ)} ∩ {(-1 : ℝ)} = {x : ℝ | false},
ext x,
simp,
intro h, linarith,
rw this,
simp,
intro h,
have := (set.eq_empty_iff_forall_not_mem.mp h.symm),
specialize this 1,
tauto,
end

-- Q3 a)
example : (λ x:ℝ, (1 + x^2)/x^2) '' (set.univ \ {(0: ℝ)}) = {x : ℝ | 1 < x}  := begin
ext y,
simp,
split,
{
  intro h,
  cases h with x hx,
  cases hx,
  rw ← hx_right,
  have : x^2 ≠ 0, exact pow_ne_zero 2 hx_left,
  have : (1 + x^2)/x^2 = (1/(x^2)) + 1,
  {
    field_simp,
  },
  rw this,
  have : x^2 > 0, exact (sq_pos_iff x).mpr hx_left,
  have : 1/x^2 > 0, exact one_div_pos.mpr this,
  linarith,
},
{
  intro hy,
  use (1/(y-1).sqrt),
  split,
  have : y - 1 > 0, linarith,
  have : (y - 1).sqrt ≠ 0, exact real.sqrt_ne_zero'.mpr this,
  exact one_div_ne_zero this,

  have : y - 1 > 0, linarith,
  simp [real.sq_sqrt],
  rw [real.sq_sqrt],
  have : y - 1 ≠ 0, exact ne_of_gt this,
  field_simp,
  exact le_of_lt this,
},
end

#check list.all₂_iff_forall


theorem list.all_iff_all₂ {α : Type*} (l : list α) (p : α → bool) : (l.all p) = tt ↔ l.all₂ (λ x, p x) := begin
simp [list.all, list.all₂],
induction l,
simp,
rw [list.foldr_cons, list.all₂_cons],
rw ← l_ih,
simp,
end

theorem bruh (α : Type*) (p : α → Prop) [decidable_pred p]: (λ x, ((ite (p x) tt ff : bool) : Prop)) = λ x, p x := begin
ext x,
cases decidable.em (p x),
simp [h],
simp [h],
end
example : (![1, 2, 3, 0] : fin 4 → fin 4) = λ x : fin 4, (x + 1 : fin 4) := begin
suffices : (list.fin_range 4).all₂ (λ x, ((![1, 2, 3, 0] : fin 4 → fin 4) x) = (λ x : fin 4, (x + 1 : fin 4)) x),
have := list.all₂_iff_forall.mp this,
apply funext,
intro x,
specialize this x,
simp at this,
exact this,

-- simp [list.all₂],
have := list.all_iff_all₂ (list.fin_range 4) (λ x, if ((![1, 2, 3, 0] : fin 4 → fin 4) x = (λ x : fin 4, (x + 1 : fin 4)) x) then tt else ff),
simp [list.all, if_pos] at this,
rw bruh at this,
simp,
rw ← this,
refl,
end

example {n : ℕ} (β : Type v) [decidable_eq β] (f g : (fin n) → β):
(list.fin_range n).all (λ x, f x = g x) → f = g := begin
intro h,
suffices : (list.fin_range n).all₂ (λ x, f x = g x),
{
  have := list.all₂_iff_forall.mp this,
  ext x,
  specialize this x,
  simp at this,
  exact this,
},

have := list.all_iff_all₂ (list.fin_range n) (λ x, if (f x = g x) then tt else ff),
simp [list.all, if_pos] at this,
rw bruh at this,
rw ← this,

exact h, 
end
#check set.Icc