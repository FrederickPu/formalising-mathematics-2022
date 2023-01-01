import .finite_cardinals

open_locale cardinal
open classical
open function

noncomputable theory

variables {A B : Type}

example (s ι : set A) (h : s = ι) : ∀ x : A, x ∈ s ↔ x ∈ ι :=
begin
rw set.ext_iff at h,
exact h,
end

lemma card_eq_iff_image_inj (ι : set A) (s : set A) (f : A → A) :
f '' ι = s → injective f → # ↥ ι  = # ↥ s :=
begin
intros p q,
rw card_eq_iff_bij,

rw set.ext_iff at p,
have :  ∀(x : A), x ∈ ι → f x ∈ s,
{
  intro x, intro h,
  rw ← p (f x), rw set.mem_image,
  use x, tauto,
},

use λ i, ⟨(f i.val), this i.val i.property⟩,
split,
{
  intros a b h,
  simp at *,
  cases a with a ha, cases b with b hb,
  simp, simp at h,
  exact q h,
},
{
  intro b,
  specialize p b.val,
  have := b.property,
  rw ← p at this,
  rw set.mem_image at this,
  cases this with a ha,
  simp,
  use a, use ha.left,
  apply subtype.eq, simp,
  rw ha.right, refl,
},
end

lemma finset_size (n : ℕ) : # ↥ {k : ℕ | k < n} = # (fin n) :=
begin
apply card_eq_iff_bij,
have : ∀ k : ℕ, k ∈ {k : ℕ | k < n}  → k < n,
{
  intro k,
  simp only [imp_self, set.mem_set_of_eq],
},

use λ x, ⟨x.val, this x.val x.property⟩,
split,
{
  intros a b,
  simp only [imp_self, fin.val_eq_coe, fin.eta],
},
{
  intro b,
  use b.val,
  simp only [fin.val_eq_coe, set.mem_set_of_eq],
  exact b.property,

  simp only [fin.val_eq_coe, fin.eta],
},
end

lemma fin_rep_set (n : ℕ) (p : ℕ → Prop):
# ↥{k : ℕ | p k ∧ k < n} = # {x : fin n | p x.val} :=
begin
apply card_eq_iff_bij,

have h1 : ∀ k : ℕ, k ∈ {k : ℕ | p k ∧ k < n} → p k,
  simp only [set.mem_set_of_eq],
  tauto,
have h2 : ∀ k : ℕ, k ∈ {k : ℕ | p k ∧ k < n} → k < n,
  simp only [set.mem_set_of_eq],
  tauto,  
use λ k, ⟨⟨k.val, h2 k.val k.property⟩, h1 k.val k.property⟩,

split,
{
  intros a b,
  simp, 
  exact subtype.eq,
},
{
  intro b, use b.val,

  exact ⟨b.property, b.val.property⟩,
  simp only [subtype.coe_eta, subtype.val_eq_coe],
},
end

lemma l1 : ↑6 = # ↥{n : ℕ | ∃ k : ℕ, n = 3*k ∧ n < 16} :=
begin
rw ← cardinal.mk_fin 6,
have : # (fin 6) = # {n : ℕ | n < 6},
exact (finset_size 6).symm,
rw this,

apply card_eq_iff_image_inj _ _ (λ k, 3*k),
ext n,
simp,
split,
{
  rintros ⟨x, ⟨h1, h2⟩⟩,
  use x, linarith,
  linarith,
},
{
  rintro ⟨⟨x,h1⟩, h2⟩,
  use x, 
  exact ⟨by linarith, by linarith⟩,
},

intros a b,
dsimp,
intro p,
linarith,
end

example : {n : ℕ | n < 4} ≃ {n : ℕ | ∃ k : ℕ, n = 5*k ∧ n < 16} :=
begin
sorry
end
lemma l2 : ↑4 = # ↥{n : ℕ | ∃ k : ℕ, n = 5*k ∧ n < 16} :=
begin
rw ← cardinal.mk_fin 4,
have : # (fin 4) = # {n : ℕ | n < 4},
exact (finset_size 4).symm,
rw this,

apply card_eq_iff_image_inj _ _ (λ k, 5*k),
ext n,
simp,
split,
{
  rintros ⟨x, ⟨h1, h2⟩⟩,
  use x, linarith,
  linarith,
},
{
  rintro ⟨⟨x,h1⟩, h2⟩,
  use x, 
  exact ⟨by linarith, by linarith⟩,
},

intros a b,
dsimp,
intro p,
linarith,
end

example : (6:ℚ) = |↥{n : ℕ | ∃ k : ℕ, n = 3*k ∧ n < 16}| :=
begin
rw [ratcard_def, nat.card],
rw ← l1,
rw cardinal.to_nat_cast,
simp,
end

example : (4:ℚ) = |↥{n : ℕ | ∃ k : ℕ, n = 5*k ∧ n < 16}| :=
begin
rw [ratcard_def, nat.card],
rw ← l2,
rw cardinal.to_nat_cast,
simp,
end

lemma fin2_cases : ∀ a : fin 2, a = 0 ∨ a = 1 :=
begin
intro a, cases a,
cases a_val,
tauto,
right,
have : nat.succ a_val > 0, exact nat.succ_pos a_val,
apply subtype.eq, simp,
linarith,
end

lemma fin2_zero_ne_one : (0 : fin 2) ≠ (1 : fin 2) :=
begin
intro p,
have h : ↑0 = (0 : fin 2), refl,
have h1: ↑1 = (1 : fin 2), refl,
rw [← h, ← h1] at p,
simp only [nat.one_ne_zero, nat.cast_zero, fin.zero_eq_one_iff, nat.cast_one] at p,
exact p,
end

example (P Q : Prop) : P ∨ Q → ¬ P → Q :=
begin
exact or.resolve_left,
end

example (α : Type) (s : set α) : cardinal.mk (↥ 𝒫 s) = (2:cardinal) ^ cardinal.mk ↥s :=
begin
exact (cardinal.mk_congr (equiv.set.powerset s)).trans cardinal.mk_set,
end

example {α : Type} : #(set α) = 2 ^ #α :=
begin
rw set,
rw cardinal.mk_arrow,
simp only [cardinal.lift_uzero, cardinal.mk_Prop],
end 