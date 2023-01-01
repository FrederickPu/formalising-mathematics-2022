import set_theory.cardinal
import set_theory.cardinal_ordinal
import data.finset.basic
import set_theory.fincard
import logic.function.basic

import data.real.basic
import data.nat.parity
import data.int.parity

#check cardinal.mk ℕ
#check cardinal.mk ℝ

open_locale cardinal
open classical
open function

variables {A B : Type}

-- standard cardinality notation
noncomputable def ratcard (α : Type*):= (nat.card α : ℚ) 
notation `|`a`|` := ratcard a
-- note we only do this for finite sets so that
-- whenever you see | | you know that u can use (+, -, *, /)

#check bijective
lemma card_le_iff_inj : # A ≤ # B ↔ ∃ f : A → B, injective f :=
begin
split,
{
  rw cardinal.le_def,
  intro p,
  apply nonempty.elim p,

  intro f', 
  cases f' with f f_inj,
  exact ⟨f, f_inj⟩,
},
{
  intro p,
  rw cardinal.le_def,
  cases p with f hf,
  apply nonempty.intro,
  exact ⟨f, hf⟩,
},
end

lemma surjective_iff_inv_inj : (∃ f : A → B, surjective f) → (∃ f' : B → A, injective f') :=
begin
rintros ⟨f, ph⟩,

-- rw surjective at ph,
have := axiom_of_choice ph,
simp only at this,
cases this with f', use f',

intros a b h,
have := congr_arg f h,
rw [this_h a, this_h b] at this,
exact this,
end

lemma card_eq_iff_bij : (∃ f : A → B, bijective f) → # A = # B :=
begin
rintros ⟨f, ⟨pinj, psur⟩⟩,
rw le_antisymm_iff, split,
{
  rw card_le_iff_inj,
  use f, exact pinj,
},
{
  rw card_le_iff_inj,
  apply surjective_iff_inv_inj,
  use f, exact psur,
},
end

variables (n m : ℕ)

def frick : fin n ⊕ fin m → fin (n+m) :=
begin
  intro x,
  cases x,
  { -- fin n -> 0, ... n
    have := x.val.lt_add_right n m x.property,
    exact ⟨x.val, this⟩
  }, -- fin m -> n ... n+m
  {
    have : n+x.val < n+m, exact add_lt_add_left x.property n,
    exact ⟨n+x.val, this⟩,
  },
end

example : # (fin n) = n :=
begin
exact cardinal.mk_fin n,
end

example : # (fin n ⊕ fin m) = # (fin n) + # (fin m) :=
begin
exact (cardinal.add_def (fin n) (fin m)).symm,
end

example : # (fin n ⊕ fin m) = # (fin (n + m)) :=
begin
rw (cardinal.add_def (fin n) (fin m)).symm,
simp only [cardinal.mk_fin],
push_cast,
end

example : # (fin n) + # (fin m) = # (fin (n + m)) :=
begin
simp only [cardinal.mk_fin],
push_cast,
end

example : # (fin n × fin m) = # (fin n) * # (fin m):=
begin
exact (cardinal.mul_def (fin n) (fin m)).symm,
end

example : # (fin n × fin m) = # (fin n) * # (fin m):=
begin
exact (cardinal.mul_def (fin n) (fin m)).symm,
end

example : # (fin n × fin m) = # (fin (n*m)):=
begin
rw ← (cardinal.mul_def (fin n) (fin m)),
simp only [cardinal.mk_fin],
push_cast,
end

example : # (fin n → fin m) = (# (fin m)) ^ (# (fin n)):=
begin
exact (cardinal.power_def (fin m) (fin n)).symm,
end

example : # (fin n → fin m) = # (fin (m^n)):=
begin
rw ← cardinal.power_def (fin m) (fin n),
simp only [cardinal.mk_fin],
push_cast, refl,
end

def ten := fin 10
def five0 := subtype (λ x : fin 10, x.val < 5)
def five1 := subtype (λ x : fin 10, 5 ≤ x.val ∧ x < 10)

lemma lf (x : ℕ) : x < 5 → x < 10 :=
begin
intro,
exact (nat.lt_add_left x 5 5) ᾰ,
end
def fivelift : five0 → fin 5 := λ x : five0, ⟨x.val, x.property⟩
def fivepull : fin 5 → five0 := λ x : fin 5, ⟨⟨x.val, lf x.val x.property⟩, x.property⟩

example : # five0 = # (fin 5) :=
begin
rw five0,
rw le_antisymm_iff,
simp only [cardinal.le_def],

split,
apply nonempty.intro,
use fivelift,
intros a b,
cases a, cases b,
rw fivelift,
dsimp,
intro,
push_cast,
cases a_val, cases b_val,
push_cast at ᾰ,

apply subtype.eq, -- important lemma1
simp,
exact fin.mk.inj_iff.mp ᾰ, -- important lemma2


apply nonempty.intro,
use fivepull,
intros a b,
cases a, cases b,
rw fivepull,
dsimp,
intro,
apply subtype.eq, simp, -- important lemma
push_cast at ᾰ,
exact fin.mk.inj_iff.mp ᾰ, -- important lemma
end
-- keep the two above lemmas in mind (and look at their proofs)

-- if there is an injection f : A → B
-- then A can be treated as a subtype of B
def inj_to_sub (f : A → B) (h : injective f) : Type* := subtype (λ b : B, ∃ a : A, f a = b)
lemma card_eq_of_inj_to_sub {f : A → B} (h : injective f) : # A = # (inj_to_sub f h) :=
begin
rw card_eq_iff_bij,
use λ a, ⟨f a, by use a, rfl⟩,
split,
{
  intros a b,
  dsimp,
  intro p,
  have : f a = f b := by exact subtype.mk.inj p, -- important lemma
  exact h this,
},
{
  intro b,
  rw injective at h,
  dsimp,
  cases b.property with a ha, use a,
  apply subtype.eq,
  simp, rw ha, simp,
},
end

#check xor ff tt
-- subtypes and subsets on a given predicate are of equal size in a given universe
lemma subtype_cardeq_set (p: B → Prop) : # ↥{x : B | p x} = # (subtype p):=
begin
rw card_eq_iff_bij,
use λ x, ⟨x.val, x.property⟩,
dsimp,
split,
{
  intros a b, simp only [imp_self, subtype.coe_eta],
},
{
  intros b, simp,
  use b, use b.property, apply subtype.eq, 
  dsimp only, refl,
},
end

-- inclusion exclusion principle
lemma in_ex (n : ℕ) (s1 s2 : set (fin n)) : # ↥ (s1 ∪ s2) + # ↥(s1 ∩ s2) = # ↥s1 + # ↥s2 :=
begin
exact cardinal.mk_union_add_mk_inter,
end

-- example of moving the cast outside
example (n m : ℕ): (n:cardinal) + (m:cardinal) = (n+m : cardinal):=
begin
rw ← nat.cast_add,
end

-- now we work on conversions between nats and cardinals
-- note: lean is kinda soft with the distinctino between cardinals and ordinals
example (c : cardinal): c < ω → ↑(cardinal.to_nat c) = c :=
begin
exact cardinal.cast_to_nat_of_lt_omega,
end

lemma to_nat_distrb_of_lt_omega (c d : cardinal): c < ω → d < ω → cardinal.to_nat (c + d) = cardinal.to_nat c + cardinal.to_nat d :=
begin
intros p q,
rw ← cardinal.cast_to_nat_of_lt_omega p,
rw ← cardinal.cast_to_nat_of_lt_omega q,

rw ← nat.cast_add (cardinal.to_nat c) (cardinal.to_nat d),
simp only [cardinal.to_nat_cast],
end

-- fin canceling
example (n : ℕ): (# (fin n)).to_nat = n:=
begin
simp only [cardinal.to_nat_cast, cardinal.mk_fin],
end

example (n : ℕ) : # (fin n) < ω := 
begin
simp only [cardinal.mk_fin],
exact cardinal.nat_lt_omega n,
end

lemma set_fin_fin (n : ℕ) (s : set (fin n)): # ↥s < ω := 
begin
have p :  # ↥s ≤ # (fin n),
exact cardinal.mk_set_le s,
have q := cardinal.nat_lt_omega n,
simp at p,
exact gt_of_gt_of_ge q p,
end

example (n m : ℕ) (s1 s2 : set (fin n)) : # ↥(s1 ∪ s2) < ω :=
begin
exact set_fin_fin n (s1 ∪ s2),
end

-- inclusion exclusion for finite/natural cardinalities
lemma in_ex_fin (n : ℕ) (s1 s2 : set (fin n)) : nat.card ↥ (s1 ∪ s2) + nat.card ↥(s1 ∩ s2) = nat.card ↥s1 + nat.card ↥s2 :=
begin
-- take the cardinal inclusion exclusion and plug it into cardinal.to_nat
have := in_ex _ s1 s2,
have := congr_arg cardinal.to_nat this,
rw to_nat_distrb_of_lt_omega at this,
rw to_nat_distrb_of_lt_omega at this,
simp [nat.card], -- then unfold the definition of nat.card
exact this, -- the rest is trivial

-- proving that all terms are finite
exact set_fin_fin n s1,
exact set_fin_fin n s2,

exact set_fin_fin n (s1 ∪ s2),
exact set_fin_fin n (s1 ∩ s2),
end

lemma ratcard_def (α : Type*) : |α| = nat.card α := 
begin
refl,
end

lemma in_ex_fin' (n : ℕ) (s1 s2 : set (fin n)) : 
|↥(s1 ∪ s2)| = |↥(s1)| + |↥(s2)| - |↥(s1 ∩ s2)|:=
begin
have := in_ex_fin n s1 s2,
have := congr_arg (λ n : ℕ, (↑n : ℚ)) this,
simp at this,

simp [ratcard_def],
linarith,
end

def triple : set (fin 16) := {n : fin 16 | n.val % 3 = 0}
def fiven : set (fin 16) := {n : fin 16| n.val % 5 = 0}
example : |↥ (triple ∪ fiven)| = |↥triple| + |↥fiven| - |↥ (triple ∩ fiven)| :=
begin
exact in_ex_fin' 16 triple fiven,
end

lemma mod_iff_mul (n d: ℕ) : n % d = 0 ↔  ∃ k : ℕ, n = d*k :=
begin
  split,
  intro p,
  have : d ∣ n, exact nat.dvd_of_mod_eq_zero p,
  have := nat.div_mul_cancel this,
  use n/d, rw mul_comm, exact this.symm,

  intro p,
  cases p with k hk,
  rw ← hk.symm, simp,
end

example (k : ℕ): 3*k ≤ 15 ↔ k ≤ 5:=
begin
split,
intro, 
linarith,
intro, 
linarith,
end

example : triple = {n : fin 16 | ∃ k : ℕ, n.val = 3*k} :=
begin
ext a,
simp [triple],
exact mod_iff_mul a 3,
end

example : # (fin 6) = # ↥{n : fin 16 | ∃ k : ℕ, n.val = 3*k} :=
begin
rw card_eq_iff_bij,
have : ∀ x : ℕ, x < 6 → 3*x < 16,
intros,
linarith,

use λ x : fin 6, ⟨⟨3*x.val, this x x.property⟩, by use x.val⟩,
split,
{
  intros a b,
  simp only [mul_eq_mul_left_iff, subtype.mk_eq_mk, or_false, nat.bit1_ne_zero],
  exact subtype.eq, 
},
{
  simp only [fin.val_eq_coe],
  rintro ⟨b, hb⟩,
  simp at hb,
  cases hb with k hk,
  use k, simp only [subtype.mk_eq_mk],
  apply subtype.eq,
  simp only [fin.val_eq_coe],
  rw hk,
  have := b.property,
  have : k < 6, simp at this,
  linarith,
  simp,
  exact nat.mod_eq_of_lt this,
},
end

-- naive proof:
-- do you see the problem?
-- there are two injections to prove
-- in each surjection there are 4 cases.
-- so overall 2*4 = 8 cases!
example : # ℕ = # ℤ :=
begin
  rw le_antisymm_iff,

  split,
  rw card_le_iff_inj,
  use (λ x, ite (even x) x (-(x+1)/2)),
  intros a b,
  dsimp,
  intro p,
  have := ite_eq_iff.mp p,
  cases this,
  {cases this,
  cases ite_eq_iff.mp this_right.symm,
  exact int.coe_nat_inj (eq.symm h.right),

  exfalso,
  cases h,
  have : (b+1 : ℤ) > 0, exact int.succ_coe_nat_pos b,
  have : -(b+1 : ℤ) < 0, exact neg_lt_zero.mpr this,
  have : (-(b+1 : ℤ))/2 < 0, exact int.div_neg' this zero_lt_two,
  rw h_right at this,
  linarith,
  },
  {
    cases this,
    cases ite_eq_iff.mp this_right.symm,
    exfalso,
    have : -(↑a + 1:ℤ) / 2 < 0 := int.div_neg' (neg_lt_zero.mpr (int.succ_coe_nat_pos a)) zero_lt_two,
    rw ← h.right at this,
    linarith,

    cases h,
    have : -(↑b + 1 : ℤ) = -(↑a + 1),
    rw nat.not_even_iff at h_left,
    rw not_even_iff.mpr a at this_left,

  }
end