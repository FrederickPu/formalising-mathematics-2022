import tactic

def deci_cong_aux (f g : ℕ → fin 2) : Prop :=
∃ k : ℕ, ((∀ i < k, f i = g i) ∧ f k = 0 ∧ g k = 1 ∧ (∀ i > k, f i = 1 ∧ g i = 0))

#print deci_cong_aux
def deci_cong (f g : ℕ → fin 2) : Prop := 
f = g ∨ deci_cong_aux f g ∨ deci_cong_aux g f 

def just_zeros (k : ℕ) (f : ℕ → fin 2) : Prop :=
(λ n, f (n + k)) = λ _, 0

def just_ones (k : ℕ) (f : ℕ → fin 2) : Prop :=
(λ n, f (n + k)) = λ _, 1

example (f g : ℕ → fin 2) : deci_cong_aux f g ↔ 
∃ k : ℕ, ((∀ i < k, f i = g i) ∧ f k = 0 ∧ g k = 1 ∧ just_ones (k+1) f ∧ just_zeros (k + 1) g) := begin
simp only [deci_cong_aux],
suffices : ∀ k : ℕ, ((∀ i > k, f i = 1 ∧ g i = 0) ↔ just_ones (k+1) f ∧ just_zeros (k+1) g),
split,
{
intro h,
cases h with k h,
use k,
rw this k at h,
exact h,
},
{
intro h,
cases h with k h,
use k,
rw ← this k at h,
exact h,
},
intro k,
split,
{
  intro h,
  simp [just_zeros, just_ones],
  split,
  ext,
  specialize h (x + k + 1) (by linarith),
  rw ← h.left,
  refl,
  ext,
  specialize h (x + k + 1) (by linarith),
  rw ← h.right,
  refl,
},
{
  intro h,
  intro x,
  intro p,
  simp [just_ones] at h,
  have l := congr_fun h.left (x - (k+1)),
  simp at l,
  have : x ≥ (k + 1), linarith,
  have : x - (k+1) + (k + 1) = x, exact nat.sub_add_cancel this,
  rw this at l,
  have r := congr_fun h.right (x - (k + 1)),
  simp at r,
  rw this at r,
  exact ⟨l, r⟩,
},
end  


#check decidable_rel