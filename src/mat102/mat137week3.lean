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
example (a b : ℕ) : b ≠ 0 → share_p a b → ∃ a' b' : ℕ, b' < b ∧ (a' : ℚ) / (b' : ℚ) < (a : ℚ) / (b : ℚ) := begin
intros w h,
rcases h with ⟨p, ⟨hp, ⟨ha, hb⟩⟩⟩,
use (a / p), use (b / p),
split,
have l : p * (b / p) = b, exact nat.mul_div_cancel' hb,
suffices : b / p < p * (b/p),
exact eq.trans_gt l this,
suffices : 1 * (b / p)  < p * (b/p), linarith,
have : b ≠ 0, exact w,
have : b / p ≠ 0, exact oops b p w hb,
suffices : 1 < p,

end  

example (a b : ℤ) (hb : b ≠ 0): ∃ p q : ℤ, q ≠ 0 ∧ (a : ℚ) / (b : ℚ) = (p : ℚ) / (q : ℚ) := begin
suffices : ¬ (∀ p q : ℤ,  ¬ (q ≠ 0 ∧ ((a : ℚ) / (b : ℚ) = (p : ℚ) / (q : ℚ) ))),
tauto,
intro h,

end