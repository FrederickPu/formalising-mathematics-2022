import tactic
import set_theory.cardinal

noncomputable theory
open_locale cardinal
open function

def pfinset (n : ℕ) : set ℕ := {x : ℕ | x < n}
notation `[`n`]` := pfinset n

namespace set

universes u v
variables {α : Type u} (p : set α → Prop) (a : α)

@[simp]
lemma split : 
{s : set α | p s ∧ a ∈ s} ∪ {s : set α | p s ∧ ¬a ∈ s} 
= {s : set α | p s}:=
begin
symmetry,
ext s,
split,
{ 
  intro hp,
  have := em (a ∈ s),
  rcases em (a ∈ s),
  left, exact ⟨hp, h⟩,
  right, exact ⟨hp, h⟩,
},
{
  intro hp,
  cases hp;
  exact hp.left,
},
end

#print split

lemma split_disjoint : 
disjoint {s : set α | p s ∧ a ∈ s} {s : set α | p s ∧ ¬a ∈ s} :=
begin
rw set.disjoint_iff_inter_eq_empty,
ext x,
split,
{simp, tauto},
{tauto},
end

example (s : set α) (f : α → α) (h : injective f):
s ≃ f '' s :=
begin
-- exact equiv.set.image f s h,
exact equiv.set.image_of_inj_on,
end

@[simp] -- needs simp tag to be reduced b/c noncomputable
noncomputable def fappend (a : α) : 
set α → set α := 
λ s : set α, s ∪ {a}

lemma singleton_elim (X : set α) (h : a ∉ X):
∀ x, x ∈ X ∪ {a} → x ≠ a → x ∈ X :=
begin
intros x p q,
simp at p,
cases p, 
exfalso, exact q p,
exact p,
end

theorem append_img_inj_on (A : set (set α))  (h : ∀ s ∈ A, a ∉ s) : 
A ≃ (fappend a) '' A :=
begin
apply equiv.set.image_of_inj_on (fappend a) A,
intros X hX Y hY,

simp only [fappend],
intro p,
have aX := h X hX, have aY := h Y hY,
ext x,
rw set.ext_iff at p,
specialize p x,

split,
{
  intro,
  have : x ∈ X ∪ {a}, exact mem_union_left _ ᾰ,
  rw p at this,
  apply singleton_elim a Y aY x this,
  {intro l, rw ← l at aX, 
  exact aX ᾰ},
},
{ -- literally just copy pasted the other case put replaced X with Y
  intro,
  have := mem_union_left _ ᾰ,
  rw ← p at this,
  apply singleton_elim a X aX x this,
  {intro l, rw ← l at aY, 
  exact aY ᾰ},
},
end

lemma l1 (A : set (set α)) (h : ∀ s ∈ A, a ∉ s): 
(fappend a) '' A = {s : set α | ∃ ι ∈ A, s = ι ∪ {a}} :=
begin
  ext x,
  simp only [fappend, exists_prop, mem_set_of_eq, mem_image],
  split;
  tauto,
end

example (A : set (set α)) (h : ∀ s ∈ A, a ∉ s): 
 A ≃ {s : set α | ∃ ι ∈ A, s = ι ∪ {a}} :=
begin
have p := append_img_inj_on a A h,
have q := l1 a A h,
rw ← q,
exact p,
end

lemma and_in_and {s : set α} {p q : set α → Prop}: 
s ∈ {s : set α | p s ∧ q s} ↔ s ∈ {s : set α | p s} ∧ s ∈ {s : set α | q s} :=
begin
simp only [iff_self, set.mem_set_of_eq],
end

lemma remove_subset (x : α) (s : set α) : #↥(s \ {x}) ≤ # ↥s :=
begin
have := set.diff_subset s {x},
exact cardinal.mk_le_mk_of_subset this,
end

lemma finite_remove_singleton (s : set α) (x : α): # ↥s < ω →  #↥(s \ {x}) < ω :=
λ p, gt_of_gt_of_ge p (remove_subset x s)

end set


namespace cardinal

universes u v
variables {α : Type u} (p : set α → Prop) (a : α)

lemma mk_pfin (n : ℕ) : # [n] = ↑n :=
begin
simp only [pfinset, mk_fintype, finset.card_range, fintype.card_of_finset],
end

lemma le_pfin (n : ℕ) (s : set ℕ) : s ⊆ [n] → # ↥s ≤ ↑n :=
begin
intro,
rw ← mk_pfin,
exact mk_le_mk_of_subset ᾰ,
end 

lemma set_split : # ↥{s : set α | p s} 
= # ↥{s : set α | p s ∧ a ∈ s} + # ↥{s : set α | p s ∧ ¬a ∈ s} :=
begin
rw ← cardinal.mk_union_add_mk_inter,
rw set.disjoint_iff_inter_eq_empty.mp (set.split_disjoint p a),
simp only [set.split, add_zero, mk_emptyc],
end

lemma mk_diff_add_mk {S T : set α} (h : T ⊆ S) : #(S \ T : set α) + #T = #S :=
(cardinal.mk_union_of_disjoint $ by exact disjoint_sdiff_self_left).symm.trans $ by rw set.diff_union_of_subset h


end cardinal

namespace pfinset

lemma equiv_singleton (n : ℕ) : ↥({n}: set ℕ) ≃ (fin 1) :=
{
  to_fun := λ n, 0,
  inv_fun := λ x,  by {exact ⟨n, rfl⟩},
  left_inv := by {intro x, simp},
  right_inv := by {intro x, simp},
}

lemma inter_singleton_succ (n : ℕ)  (ι : set ℕ) :
ι ⊆ [n] → ι ∩ {n} = ∅ := 
begin
intro p, ext x,
split,
simp [set.subset_def, pfinset] at p,
specialize p x,
simp,
intros h h', have := p h,
rw h' at this, exact nat.lt_asymm (this) this,
simp,
end

lemma union_singleton_card (n : ℕ) (ι : set ℕ) :
ι ⊆ [n] → # ↥(ι ∪ {n}) = #ι+↑1 :=
begin
have : #↥{n} = ↑1,
rw ← cardinal.mk_fin,
apply cardinal.mk_congr,
exact equiv_singleton n,

rw ← this,
rw ← cardinal.mk_union_add_mk_inter,
intro,
suffices : ↑ 0 = # ↥(ι ∩ {n}),
rw ← this, simp,

rw ← cardinal.mk_fin,
suffices : ι ∩ {n} = ∅,
simp [this, cardinal.mk_emptyc],

exact inter_singleton_succ n ι ᾰ,
end

@[simp]
lemma insert_singleton_card {n : ℕ} {ι : set ℕ} :
ι ⊆ [n] → # ↥(insert n ι) = #ι+↑1 :=
begin
rw ← set.union_singleton,
exact union_singleton_card n ι,
end

lemma union_singleton_sub (n : ℕ) (ι : set ℕ) :
ι ⊆ [n] → ι ∪ {n} ⊆ [n+1] :=
begin
intros p x hx,
cases hx,
  exact nat.lt.step (p hx),

  simp at *, rw hx,
  exact lt_add_one n,
end

@[simp]
lemma insert_singleton_sub {n : ℕ} {ι : set ℕ} :
ι ⊆ [n] → insert n ι ⊆ [n+1] :=
begin
rw ← set.union_singleton,
exact union_singleton_sub n ι,
end

lemma sub_of_sub_pred (n : ℕ) (qval : set ℕ): 
qval ⊆ [n - 1] → qval ⊆ [n] :=
begin
  intro,
  have : [n-1] ⊆ [n],
  intro x,
  simp [pfinset], exact nat.lt_of_lt_pred,
  exact set.subset.trans ᾰ this,
end

lemma subset_succ_union (n : ℕ) : [n] ∪ {n} = [n+1] :=
begin
ext x,
split,
{
  rintros (p | q),
  exact nat.lt.step p,
  simp [pfinset] at *,
  rw q, exact lt_add_one n,
},
{
  intro p,
  have : x ≤ n, exact nat.lt_succ_iff.mp p,
  simp [pfinset],
  exact eq_or_lt_of_le this,
},
end

@[simp]
lemma subset_succ_insert {n : ℕ} : insert n [n] = [n+1] :=
begin
rw ← set.union_singleton,
exact subset_succ_union n,
end

lemma split (n k : ℕ) (s : set ℕ) (h1: s ⊆ [n + 1])
(h2: # ↥s = ↑k + 1) :
 {x : ℕ | x ∈ s ∧ ¬x = n} ∪ {x : ℕ | x ∈ s ∧ x = n} = {x : ℕ | x ∈ s} :=
begin
ext x,
simp,
tauto,
end

lemma split_subset (n k : ℕ) (s : set ℕ) (h1: s ⊆ [n + 1])
(h2: # ↥s = ↑k + 1) :
{x : ℕ | x ∈ s ∧ ¬x = n} ⊆ {x : ℕ | x ∈ s} :=
begin
rw ← pfinset.split n k s h1 h2,
exact set.subset_union_left _ _,
end

lemma end_remove (s : set ℕ) (n k : ℕ) : n ∉ s ∧ s ⊆ [n + 1] ↔ s ⊆ [n] :=
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

end pfinset