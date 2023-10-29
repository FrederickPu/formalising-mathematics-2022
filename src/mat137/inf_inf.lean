import data.real.basic

-- limit as x approaches a of f x = ∞
def approach_inf (f : ℝ → ℝ) (a : ℝ) := ∀ M > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → f x > M 
def approach_neg_inf (f : ℝ → ℝ) (a : ℝ) := ∀ M < 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → f x < M

-- limit as x -> a of f x = L
def limit (f : ℝ → ℝ) (a L : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε 

def limitR (f : ℝ → ℝ) (a L : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < x - a ∧ x - a < δ → |f x - L| < ε 
def limit_inf (f : ℝ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ M > 0, ∀ x : ℝ, M < x → |f x - L| < ε 

def continuous_on (f : ℝ → ℝ) (D : set ℝ) := ∀ a ∈ D, limit f a (f a) -- limit as x -> a of f x = f a
theorem cont_subset (f : ℝ → ℝ) (C D : set ℝ) : (C ⊆ D) → continuous_on f D → continuous_on f C := begin
intro hCD,
intro h1,
intros x hx,
exact h1 x (hCD hx),
end

example (f g : ℝ → ℝ) (a : ℝ) (h1 : f ≤ g) (h2 : approach_neg_inf g a): (approach_neg_inf f a) := begin
intros M hM,
specialize h2 M hM,
rcases h2 with ⟨δ, hd, H⟩,
use δ, use hd,
intro x,
intro hx,
specialize H x hx,
specialize h1 x,
exact gt_of_gt_of_ge H h1,
end


axiom IVT (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) (hC : continuous_on f (set.Ioo a b)): ∀ c : ℝ, f a < c ∧ c < f b → ∃ x ∈ (set.Ioo a b), f x = c
axiom IVT' (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) (hC : continuous_on f (set.Ioo a b)): ∀ c : ℝ, f a > c ∧ c > f b → ∃ x ∈ (set.Ioo a b), f x = c
axiom EVT (f : ℝ → ℝ) (a b : ℝ) (h : a ≤ b) (hC : continuous_on f (set.Icc a b)) : ∃ x ∈ set.Icc a b, ∀ y ∈ set.Icc a b, f y ≤ f x

#check set.Ioi
#check max_ge_left
example (f : ℝ → ℝ) :
 continuous_on f (set.Ioi (-7: ℝ)) → limitR f 7 0 → limit_inf f 1
 → f 12 = 345 → 
 (∃ x y ∈ set.Ioi (-7 : ℝ), x ≠ y ∧ f x = 77 ∧ f y = 77)  := begin
 intros hfC hR hI f12,
 specialize hR 1 (by linarith),
 rcases hR with ⟨δ, hd, H⟩,
 have crux1 : f (min (δ / 2 + 7) 8) < 1,
 {
  specialize H (min (δ / 2 + 7) 8),
  have := min_le_left (δ / 2 + 7) 8,
  simp at H,
  specialize H (by linarith) (by linarith) (by {
    cases min_cases (δ / 2 + 7) 8,
    linarith [h.left],
    linarith [h.left],
  }),
    exact lt_of_abs_lt H,
 },

 specialize hI 1 (by linarith),
 rcases hI with ⟨M, hM, H'⟩,
 specialize H' (max (M + 1) 20) (by linarith [le_max_left (M+1) 20]),
 have crux2 : f (max (M + 1) 20) < 2 := by linarith [lt_of_abs_lt H'],

 have subset1 : set.Ioo (min (δ / 2 + 7) 8) 12 ⊆ set.Ioi (-7 : ℝ), {
  intros x hx,
  simp at hx,
  simp,
  cases hx.left,
  linarith, linarith,
 },
 have ivt1 := IVT f (min (δ / 2 + 7) 8) 12 (by linarith [min_le_right (δ / 2 + 7) 8]),
 specialize ivt1 (cont_subset f _ (set.Ioi (-7 : ℝ)) subset1 hfC) 77 (by {
  split,
  linarith, linarith,
 }),

 have subset2 : set.Ioo 12 (max (M + 1) 20) ⊆ set.Ioi (-7 : ℝ), 
 {
  intros x hx,
  simp at hx,
  simp,
  linarith [hx.left],
 },
 have ivt2 := IVT' f 12 (max (M + 1) 20) (by linarith [le_max_right (M + 1) 20]),
 specialize ivt2 (cont_subset f _ _ subset2 hfC) 77 (by {
  split,
  linarith, linarith,
 }),

 rcases ivt1 with ⟨x, hx, Hx⟩,
 rcases ivt2 with ⟨y, hy, Hy⟩,
 use x, use subset1 hx,
 use y, use subset2 hy,
 split,
 simp at hx, simp at hy, 
 linarith,

 exact ⟨Hx, Hy⟩,
end

example (f : ℝ → ℝ) :
 continuous_on f (set.Ioi (-7: ℝ)) → limitR f (-7:ℝ) 0 → limit_inf f 1
 → f 12 = 345 → 
 (∃ x ∈ set.Ioi (-7 : ℝ), ∀ y ∈ set.Ioi (-7 : ℝ), f y ≤ f x)  := begin
 intros hfC hR hI f12,
 specialize hR 1 (by linarith),
 rcases hR with ⟨δ, hd, H⟩,
--  have := H (min (δ / 2 - 7) 8),

 specialize hI 1 (by linarith),
 rcases hI with ⟨M, hM, H'⟩,
--  have := H' (max (M + 1) 20) (by linarith [le_max_left (M+1) 20]),

 -- part two show maximum exists
 have evt := EVT f (min (δ / 2 - 7) (-6)) (max (M + 1) 20),
 specialize evt (by linarith [min_le_right (δ / 2 - 7) (-6), le_max_right (M + 1) 20]),
 have subset3 : set.Icc (min (δ / 2 - 7) (-6)) (max (M + 1) 20) ⊆ set.Ioi (-7 : ℝ),
 {
  intro x, simp,
  intros h1 h2,
  cases h1,
  linarith, linarith,
 },
 specialize evt (cont_subset f _ _ subset3 hfC),

 rcases evt with ⟨x, hx, Hx⟩,
 use x, use subset3 hx, 

 intro y,
 intro hy,
 cases em (y ∈ set.Icc (min (δ / 2 - 7) (-6)) (max (M + 1) 20)),
 specialize Hx y,
 exact Hx h,
 simp only [set.mem_Icc, decidable.not_and_iff_or_not, not_le] at h,
 simp at hy,

 specialize Hx 12 (by {
  split,
  linarith [min_le_right (δ / 2 - 7) (-6)],
  linarith [le_max_right (M + 1) 20],
 }),
 cases h,
 specialize H y (by {
  simp at h,
  split,
  linarith [h.left, h.right],
  linarith [h.left],
 }),
 have : f y < 1:= by linarith [lt_of_abs_lt H],
 linarith only [this, Hx, f12],

 specialize H' y (by {
  linarith [le_max_left (M + 1) 20],
 }),
 linarith [lt_of_abs_lt H'],
end

#check not_le