import data.real.basic
example (a : ℕ → ℝ) : a 1 = 1 → a 2 = 8 → (∀ n ≥ 3, a n = a (n - 1) + 2*(a (n - 2))) →
∀ n, a (n+2) = 3*2^(n+1)+2*(-1)^(n+2) := begin
intro ha1, intro ha2,
intro hoop,
intro n,
induction n with d dh,
norm_num [ha2],

have := hoop (d.succ + 2) (by {
  have : d.succ > 0, exact ne_zero.pos (nat.succ d),
  linarith,
}),
norm_num at this,
rw dh at this,
end 