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
example (a b : ℕ) : b > 0 → share_p a b → ∃ a' b' : ℕ, b' < b ∧ (a' : ℚ) / (b' : ℚ) = (a : ℚ) / (b : ℚ) := begin
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

have := nat.pos_of_dvd_of_pos hb w,
have : (p:ℚ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt this),
rw [rat.coe_nat_div a p ha, rat.coe_nat_div b p hb],
field_simp,
end  

example (a b : ℤ) (hb : b ≠ 0): ∃ p q : ℤ, q ≠ 0 ∧ (a : ℚ) / (b : ℚ) = (p : ℚ) / (q : ℚ) := begin
suffices : ¬ (∀ p q : ℤ,  ¬ (q ≠ 0 ∧ ((a : ℚ) / (b : ℚ) = (p : ℚ) / (q : ℚ) ))),
tauto,
intro h,

end