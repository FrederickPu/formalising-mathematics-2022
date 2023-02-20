import data.real.basic

#check ℝ

-- limit as x -> a from the right of f(x) = b
def Rlimit (a : ℝ) (f: ℝ → ℝ) (b : ℝ) := 
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, a < x ∧ x < a + δ  → |b - f x| < ε

def Llimit (a : ℝ) (f: ℝ → ℝ) (b : ℝ) := 
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, a - δ < x ∧ x < a  → |b - f x| < ε

def limit (a : ℝ) (f : ℝ → ℝ) (b : ℝ) := 
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, (0 < |x - a| ∧ |x - a| < δ) → |b - f x| < ε

theorem RL_imp (a : ℝ) (f : ℝ → ℝ) (b : ℝ) :
Rlimit a f b → Llimit a f b → limit a f b :=
begin
intros p q,
intros ε he,
rw Rlimit at p, rw Llimit at q,
rcases p ε he with ⟨δ1, ⟨Hp, p⟩⟩,
rcases q ε he with ⟨δ2, ⟨Hq, q⟩⟩,
use min δ1 δ2,
split,
exact lt_min_iff.mpr ⟨Hp, Hq⟩,

intro x,
specialize p x, specialize q x,
intro h,
cases lt_or_ge 0 (x - a),

{
apply p,
split,
linarith,
rw abs_of_pos h_1 at h,
linarith [min_le_left δ1 δ2],
},

{
apply q,
have : x - a ≠ 0, exact abs_pos.mp h.left,
have : 0 > x - a, exact (ne.le_iff_lt this).mp h_1,
split,
rw abs_of_neg this at h,
linarith [min_le_right δ1 δ2],
linarith,
},
end