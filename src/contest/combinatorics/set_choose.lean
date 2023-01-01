import tactic
import set_theory.cardinal

import .pfinset

open_locale cardinal

def set_choose (n k: ℕ) : set (set ℕ)
:= {s : set ℕ | s ⊆ pfinset n ∧ # s = # (fin k)}

variables (n k : ℕ)
example (c d e f: cardinal) : c = d → e = f → c + e = d + f := 
begin
refine congr_arg2 (λ (c e : cardinal), c + e),
end

example (α : Type) (s ι : set α) : s = ι → # ↥s = # ↥ ι :=
begin
library_search,
end

example (α : Type) (x : α) (s ι : set α) : 
s ⊆ s ∪ ι :=
begin
exact set.subset_union_left s ι,
end

lemma split' (s : set ℕ) (h1: s ⊆ [n + 1])
(h2: # ↥s = ↑k + 1) :
 {x : ℕ | x ∈ s ∧ ¬x = n} ∪ {x : ℕ | x ∈ s ∧ x = n} = {x : ℕ | x ∈ s} :=
begin
ext x,
simp,
tauto,
end

lemma split'_subset (s : set ℕ) (h1: s ⊆ [n + 1])
(h2: # ↥s = ↑k + 1) :
{x : ℕ | x ∈ s ∧ ¬x = n} ⊆ {x : ℕ | x ∈ s} :=
begin
rw ← split' n k s h1 h2,
exact set.subset_union_left _ _,
end

lemma and_in_and {s : set ℕ} {p q : set ℕ → Prop}: 
s ∈ {s : set ℕ | p s ∧ q s} ↔ s ∈ {s : set ℕ | p s}∧ s ∈ {s : set ℕ | q s} :=
begin
simp only [iff_self, set.mem_set_of_eq],
end

lemma end_remove (s : set ℕ) : n ∉ s ∧ s ⊆ [n + 1] ↔ s ⊆ [n] :=
begin
simp [pfinset, set.subset_def],
split,
intros h x,
have : x ∈ s → x ≠ n := by {intros p q, rw q at p, exact h.left p},
have : x < n+1 → x ≠ n → x < n := λ p q, array.push_back_idx p q,
tauto,

intro h,
split,
exact λ p, nat.lt_irrefl n ((h n) p),
exact λ x p, nat.lt.step (h x p),
end


lemma remove_subset (s : set ℕ) : #↥(s \ {n}) ≤ # ↥s :=
begin
have := set.diff_subset s {n},
exact cardinal.mk_le_mk_of_subset this,
end

lemma finite_remove_singleton (s : set ℕ) (h : s ⊆ [n+1]) : #↥(s \ {n}) < ω :=
begin
have p := remove_subset n s,
have q := cardinal.mk_le_mk_of_subset h,
have r := cardinal.mk_pfin (n+1),
have l : ↑ (n+1) < ω, refine cardinal.nat_lt_omega (n+1),
rw ← r at l,
exact gt_of_gt_of_ge (gt_of_gt_of_ge l q) p,
end

@[simp]
lemma idk : insert n [n+1] = [n+1] :=
begin
rw pfinset,
simp,
end

example (s : set ℕ) (h : n ∈ s): insert n s = s :=
begin
exact set.insert_eq_of_mem h,
end

lemma remove_eq_min_one (s: set ℕ)
(h1: s ⊆ [n + 1])
(h2: # ↥s = ↑k + 1)
(h3: n ∈ s) :
# ↥(s \ {n}) = ↑k := 
begin
suffices : # ↥(s \ {n})+↑1= #↥s,
have := congr_arg (λ c, cardinal.to_nat c) this,

have l := finite_remove_singleton n s h1,
have l1 : (↑1 : cardinal) < ω := cardinal.nat_lt_omega 1,
have p := cardinal.to_nat_add_of_lt_omega l l1,
have q := cardinal.to_nat_add_of_lt_omega (cardinal.nat_lt_omega k) l1,
simp at this, simp at p, simp at q,

rw [p, h2, q] at this,
simp at this,
rw [← cardinal.cast_to_nat_of_lt_omega l, this],

have l := end_remove n (s \ {n}),
have := pfinset.union_singleton_card n (s \ {n}),
rw ← l at this,
simp at this,
simp,
rw [← this h1, set.insert_eq_of_mem h3],
end

example :
# ↥(set_choose (n+1) (k+1)) = #↥(set_choose n (k+1)) + #↥(set_choose n k) :=
begin
simp [set_choose],
have := cardinal.set_split (λ s, s ⊆ [n+1] ∧  #↥s = ↑(k + 1)) n,
simp at this,
rw this,
rw cardinal.add_comm,
apply congr_arg2 (λ (c e : cardinal), c + e),

apply congr_arg (λ (s : set (set ℕ)), # ↥s),
{
  ext s,
  simp,
  rw [and_comm, ← and_assoc],
  apply and_congr_left',
  exact end_remove n s,
},

have l : ↥{s : set ℕ | s ⊆ [n] ∧ # ↥s = ↑k} ≃ ↥(set.fappend n '' {s : set ℕ | s ⊆ [n] ∧ # ↥s = ↑k}),
{
  apply set.append_img_inj_on n ({s : set ℕ | s ⊆ [n] ∧ # ↥s = ↑k}),
  simp [and_in_and],
  exact λ s h _, ((end_remove n s).mpr h).left,
},
suffices : (set.fappend n '' {s : set ℕ | s ⊆ [n] ∧ # ↥s = ↑k}) 
= {s : set ℕ | (s ⊆ [n + 1] ∧ # ↥s = ↑k + 1) ∧ n ∈ s},
rw ← this,
exact cardinal.mk_congr (equiv.symm l),
ext s,
simp [set.fappend],
split,
{
  rintro ⟨ι, ⟨hi_left, hi_right⟩⟩,
  simp [← hi_right],
  split,
  exact pfinset.insert_singleton_sub hi_left.left,
  simp [pfinset.insert_singleton_card hi_left.left, hi_left.right],
},
{
  intro h, use (s \ {n}),
  simp [h.left.left, set.insert_eq_of_mem h.right],

  rcases h with ⟨⟨h1, h2⟩, h3⟩, 
  exact remove_eq_min_one n k s h1 h2 h3,
},
end

#check cardinal.mk_to_nat_eq_card