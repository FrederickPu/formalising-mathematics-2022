import data.real.basic
import data.real.nnreal

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

example : ∀ a, limit a (λ x, x) a :=
begin
intros x ε he,
use ε,
split,
exact he,
intros x1 h,
simp [← abs_sub_comm x1 x],
exact h.right,
end

example (a b : nnreal) : (a : ℝ) * (b : ℝ) = ((a*b) : ℝ) :=
begin
library_search,
end

theorem productrule (a b1 b2: ℝ) (f g: ℝ → ℝ) :
limit a f b1 → limit a g b2 → limit a (f*g) (b1*b2) :=
begin
intros p q,
intros ε he,
let ε1 := ε/(2*(1 + |b2|)),   
let ε2 := ε/(2*(1 + |b1|)),   
let ε3 := (1:ℝ),
have he1 : ε1 > 0,
{
simp [ε1],
apply div_pos he,
linarith [abs_nonneg b2],
},
have he2 : ε2 > 0,
{
simp [ε2],
apply div_pos he,
linarith [abs_nonneg b1],
},
have he3 : ε3 > 0, norm_num [ε3],

rcases p ε1 he1 with ⟨δ1, ⟨Hd1, h1⟩⟩,
rcases q ε2 he2 with ⟨δ2, ⟨Hd2, h2⟩⟩,
rcases q ε3 he3 with ⟨δ3, ⟨Hd3, h3⟩⟩,

use min (min δ1 δ2) δ3,
split,
{
simp only [gt_iff_lt, lt_min_iff],
tauto,
},

intro x,
specialize h1 x,
specialize h2 x,
specialize h3 x,

intro h,
end
theorem abs_bound (b ε : ℝ) :
ε > 0 → ∃δ>0, ∀ a, |a| < δ → |b| * |a| < ε :=
begin
intro he,
cases eq_or_lt_of_le (abs_nonneg b),
{
  simp [← h],
  use 1, intros,
  split,
    exact zero_lt_one,
    intros, exact he,
},
{
  use (ε/|b|),
  split,
  exact div_pos he h,

  intro a,
  exact λᾰ, (lt_div_iff' h).mp ᾰ,
},
end
example (a b1 b2: ℝ) (f g : ℝ → ℝ): 
limit a f b1 → limit a g b2 → limit a (f*g) (b1*b2) :=
begin
intros p q,
intros ε he,
suffices l : ∀ x, 
|b1 * b2 - (f * g) x| < |b1| * |b2 - g x| + |b1 - f x| * |b2|,
have hp : ε / 2 > 0, exact half_pos he,
cases abs_bound b1 (ε/2) hp with ε1 he1,
cases abs_bound b2 (ε/2) hp with ε2 he2,
specialize p ε2 (Exists.fst he2),
specialize q ε1 (Exists.fst he1),
rcases p with ⟨δ1, ⟨p, pH⟩⟩,
rcases q with ⟨δ2, ⟨q, qH⟩⟩,
use (min δ1 δ2),
split,
exact lt_min p q,

intros x hx,
have he1' := Exists.snd he1 (b2 - g x),
have he2' := Exists.snd he2 (b1 - f x),

specialize pH x,
have : |x - a| < δ1, 
  linarith [hx.right,  min_le_left δ1 δ2],
simp [hx.left, this] at pH,

specialize qH x,
have : |x - a| < δ2, 
  linarith [hx.left,  min_le_right δ1 δ2],
simp [hx.left, this] at qH,

have := he1' qH,
have := he2.snd (b1 - f x) pH,
specialize l x,
linarith,


intro x,
have : b1 * b2 - (f * g) x = b1 * (b2 - g x) + (b1 - f x) * b2,
simp, ring,
end