import data.real.basic
import data.nat.choose.dvd

-- sqrt 2 irrational

def share_p (a b : ℕ) := ∃ p ≠ 1, p ∣ a ∧ p ∣ b  



lemma oops (a p : ℕ) (ha : a > 0) : p ∣ a → a / p > 0 := begin
intro h,
cases exists_eq_mul_right_of_dvd h with k hk,
rw hk,
have : p > 0, {
  have aliif : p = 0 ∨ p > 0, exact eq_zero_or_pos,
  cases aliif,
  rw aliif at hk,
  simp at hk,
  linarith,
  
  exact aliif,
},
rw mul_comm,
rw nat.mul_div_cancel k this,
{
  have aliif : k = 0 ∨ k > 0, exact eq_zero_or_pos,
  cases aliif,
  rw aliif at hk,
  linarith,

  exact aliif,
},
end 
theorem desc (a b : ℕ) : b > 0 → share_p a b → ∃ a' b' : ℕ, b' < b ∧ b' > 0 ∧ (a' : ℚ) / (b' : ℚ) = (a : ℚ) / (b : ℚ) := begin
intros w h,
rcases h with ⟨p, ⟨hp, ⟨ha, hb⟩⟩⟩,
use (a / p), use (b / p),
split,
have l : p * (b / p) = b, exact nat.mul_div_cancel' hb,
suffices : b / p < p * (b/p),
exact eq.trans_gt l this,
suffices : 1 * (b / p)  < p * (b/p), linarith,
have  : b / p > 0, exact oops b p w hb,
suffices l : 1 < p,
exact (mul_lt_mul_right this).mpr l,
have : p > 0, exact nat.pos_of_dvd_of_pos hb w,
cases nat.succ_le_iff.mpr this,
exact false.elim (hp (refl 1)),
exact (ne.symm hp).lt_of_le _x,

split,
exact oops b p w hb,

have := nat.pos_of_dvd_of_pos hb w,
have : (p:ℚ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt this),
rw [rat.coe_nat_div a p ha, rat.coe_nat_div b p hb],
field_simp,
end  

#check is_strict_total_order
 
theorem strong (b : ℕ) : ∀ b'< b, b' > 0 → ∀ a : ℕ, ∃ p q : ℕ, (p:ℚ) / (q:ℚ) = (a:ℚ) / (b':ℚ) ∧ ¬ (share_p p q) := begin
induction b with d dh,
simp,

intros b' hb' hb'' a,
cases em (share_p a b'),
rcases desc a b' hb'' h with ⟨p, ⟨q, h⟩ ⟩,
specialize dh q (by {
  cases h,
  have : b' ≤ d, exact nat.lt_succ_iff.mp hb',
  linarith,
}) h.right.left p,
rcases dh with ⟨p', ⟨q', h'⟩ ⟩,
use p', use q',
rw ← h.right.right,
exact h',

use a, use b', 
exact ⟨refl _, h⟩,
end

theorem pff (a b : ℕ) (hb : b > 0): ∃ p q : ℕ, (p : ℚ) / (q : ℚ) = (a : ℚ) / (b : ℚ) ∧ ¬ share_p p q := begin
exact strong (b + 1) b (by linarith) hb a,
end

#check order_dual

def nat.even (a : ℕ) := ∃ k : ℕ, a = 2*k 
def nat.odd (a : ℕ) := ∃ k : ℕ, a = 2*k + 1

theorem nat.even_or_odd (a : ℕ) : a.even ∨ a.odd := begin
induction a,
left,
use 0, simp,
cases a_ih with p q,
cases p with k hk,
rw hk,
right,
use k, 

cases q with k hk,
rw hk,
left,
use (k + 1), ring,
end

theorem nat.not_even_and_odd (a : ℕ) : ¬ (a.even ∧ a.odd) := begin
rintro ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩,
rw hk1 at hk2,
have : 2*k1 - 2*k2 = 1, exact norm_num.sub_nat_pos (2 * k1) (2 * k2) 1 (eq.symm hk2),
rw ← mul_tsub 2 k1 k2 at this,
simp at this,
exact this,
end

theorem nat.even_sq (a : ℕ) : a.even → (a^2).even := begin
rintro ⟨k, hk⟩,
rw hk,
use (2*k^2),
ring,
end

theorem nat.odd_sq (a : ℕ) : a.odd → (a^2).odd := begin
rintro ⟨k, hk⟩,
rw hk,
use (2*k^2+2*k),
ring,
end

theorem nat.even_of_sq_even (a : ℕ) : (a^2).even → a.even := begin
intro h,
cases a.even_or_odd,
exact h_1,

have := nat.not_even_and_odd (a^2) ⟨h, a.odd_sq h_1⟩,
exact false.elim this,
end 

theorem nat.even_imp_div_two (a : ℕ) : a.even → 2 ∣ a := begin
rintro ⟨k, hk⟩,
exact dvd.intro k (eq.symm hk), 
end
example (a b c : ℕ) (h : c ≠ 0): c*a = c*b →  a = b := begin
intro h,
exact (mul_right_inj' h).mp h_1,
end

example (a b : ℕ) (hb : b > 0): ((a : ℚ) / (b : ℚ))^2 = 2 → share_p a b := begin
intro h,
have h' : a^2 = 2*b^2, 
{
  have : (b : ℚ) ≠ 0, exact nat.cast_ne_zero.mpr (ne_of_gt hb),
  field_simp at h,
  have : ((a^2 : ℕ) : ℚ) = ((2*b^2 : ℕ) : ℚ), simp,
  exact h, exact nat.cast_inj.mp this,
},
have : (a^2).even, 
{
  rw h',
  use b^2,
},
cases nat.even_of_sq_even a this with k hk,
rw hk at h',
ring_nf at h',
have : 2*(2*k^2) = 2*(b^2), ring, exact h',
have : 2*k^2 = b^2, exact (mul_right_inj' (ne_zero.ne 2)).mp this,
have := b.even_of_sq_even ⟨k^2, eq.symm this⟩,
have divB := b.even_imp_div_two this,
have divA : 2 ∣ a, exact dvd.intro k (eq.symm hk),
use 2,
split,
simp,
split,
exact divA,
exact divB,
end