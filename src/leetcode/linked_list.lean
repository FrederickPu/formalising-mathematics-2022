import tactic
set_option trace.eqn_compiler.elim_match true

structure linked_list :=
(head : ℕ)
(next : ℕ → ℕ)

lemma nat.iterate.succ (α : Type) (f : α → α) (n : ℕ) : (f ∘ (f^[n])) = (f^[n+1]) :=
begin
induction n with d dh,
simp [nat.iterate],
ext x,
simp [nat.iterate],

ext x,
simp [nat.iterate],
have : ∀ (x y z : α → α) (a : α), (x ∘ y) (z a) = x (y (z a)),
intros x y z, intro a,
have : (x ∘ y) (z a) = (x ∘ y ∘ z) a, exact rfl,
rw this,

rw [← this f _ f, ← this (f^[d]) f f],
rw dh, rw nat.iterate,
end

lemma nat.iterate.hom (α : Type) (f : α → α) (n m: ℕ) : (f^[m]) ∘ (f^[n]) = (f^[m+n]) :=
begin
induction m with d dh,
ext x,
simp [nat.iterate],

rw nat.succ_add, rw [← nat.iterate.succ, ← nat.iterate.succ α f (d + n)], 
rw function.comp.assoc,
rw dh,
end

lemma nat.iterate.hom' (α : Type) (f : α → α) (n m: ℕ) (x : α): (f^[m]) ((f^[n]) x )= (f^[m+n]) x :=
begin
rw ← function.comp_app (f^[m]),
simp only [nat.iterate.hom],
end

lemma function.comp.def {α β γ : Type} (f : α → β) (g : β → γ) (x : α): (g ∘ f) x = g (f x ) :=
begin
exact rfl,
end

namespace linked_list
variables (ll : linked_list)

def cycle_at (a : ℕ) := ∃ n : ℕ, n > 0 ∧ (ll.next^[n] a = a)

-- can be reached from the head
def reachable (a : ℕ) := ∃ n : ℕ, ll.next^[n] ll.head = a


section cycle_detection
structure two_ptr_state : Type :=
(slow : ℕ)
(fast : ℕ)
(met : bool)
(stopped : bool)

def two_ptr_step : two_ptr_state → two_ptr_state :=
λ x,
do
let ⟨slow, fast, met, stopped⟩ := x,
if stopped then x
else
        if met then 
                if slow = fast then ⟨slow, fast, tt, tt⟩
                else ⟨ll.next slow, ll.next fast, tt, ff⟩
        else
                if slow = fast then ⟨slow, fast, tt, ff⟩
                else ⟨ll.next slow, ll.next^[2] fast, ff, ff⟩

def terminates (initial : two_ptr_state) (f : two_ptr_state → two_ptr_state)
:= ∃ n : ℕ,  (f^[n] initial).stopped


example (a : ℕ) (h1 : ll.cycle_at a) (h2 : ll.reachable a) : 
∃ n : ℕ, (ll.two_ptr_step^[n] ⟨ll.head, ll.head, ff, ff⟩).stopped ∧ 
(ll.two_ptr_step^[n] ⟨ll.head, ll.head, ff, ff⟩).slow = a :=
begin
cases h2 with m' hm',

let s := {x : ℕ | x < m'+1},
let sm' := { x ∈ s | ll.cycle_at (ll.next^[x] ll.head) }, -- set of all loop indices

let fin_sm' : finset ℕ := by {
        have l : fintype ↥ s, exact set.fintype_lt_nat (m' + 1),
        have  r: sm' ⊆ s, exact set.sep_subset s (λ (x : ℕ), cycle_at ll (ll.next^[x] ll.head)),

        have : decidable_pred (λ (_x : ℕ), _x ∈ sm'),
        simp, intro x,
        exact classical.dec _,

        have := @set.fintype_subset ℕ s sm' l this r,
        exact @set.to_finset ℕ sm' this,
},

have sm'_nonempty : fin_sm'.nonempty := by 
        {use m', simp [hm'], exact h1,},
let m := finset.min' fin_sm' sm'_nonempty,

have hm : m ∈ fin_sm' := finset.min'_mem fin_sm' sm'_nonempty,
have hm1 := fin_sm'.min'_le,
simp [sm'] at hm1,

have : ∀ x y, x < y ∧ y < m →  (ll.next^[x] ll.head) ≠ (ll.next^[y] ll.head),
{
        rintros x y ⟨hx, hy⟩,
        intro h,

        have : ll.cycle_at (ll.next^[x] ll.head),
        {
                have temp : y - x > 0, exact tsub_pos_of_lt hx, 
                have : y - x + x = max y x := tsub_add_eq_max,
                rw max_eq_left_of_lt hx at this,
                rw ← this at h,
                rw ← nat.iterate.hom ℕ ll.next x (y-x) at h,

                simp only [function.comp_app] at h,
                use y - x,
                split, exact temp,
                rw ← h,
        },
        specialize hm1 x, 
        suffices :  x ≥ m, linarith,
        apply hm1,
        split,
                have : m < m' + 1, {simp at hm, exact hm.left,},
                linarith,

                exact this,
},

let junc := (ll.next^[m] ll.head), -- junction node

cases h1 with n' hn',

simp at hm,
cases hm.right with u hu,

let s' : set ℕ := {x : ℕ | x <  u + 1},
let sn' := {x ∈ s' | (ll.next^[x] junc) = junc},
let fin_sn' : finset ℕ := set.to_finset sn',

have sn'_nonempty : fin_sn'.nonempty := by {
        use u,
        simp,
        exact hu.right,
},
let n := fin_sn'.min' sn'_nonempty,
have hn : n ∈ fin_sn' := finset.min'_mem fin_sn' sn'_nonempty,
have hn1 := fin_sn'.min'_le,
simp [fin_sn'] at hn1,

have : ∀ x y,x < y ∧ y < n → (ll.next^[x] junc) ≠ (ll.next^[y] junc),
{
        intros x y,
        
        intro hxy, intro p,

        have : (ll.next^[y - x]) ((ll.next^[x]) junc)= (ll.next^[x]) junc,
                rw ← function.comp_app (ll.next^[y - x]),
                rw nat.iterate.hom,
                have : (y - x) + x = y := nat.sub_add_cancel (le_of_lt hxy.left),
                rw this,
                exact p.symm,
        have := congr_arg (ll.next^[n - x]) this,
        have : (ll.next^[(y - x) + ((n - x) + x)] junc) = (ll.next^[(n - x) + x] junc),
                simp [nat.iterate.hom'] at *,
                have l : (y - x) + ((n - x) + x) = (n - x) + (y - x) + x, ring,
                rw l, ring_nf, exact this,
        
        have l : n - x + x = n, exact nat.sub_add_cancel (by linarith),
        simp at hn,
        rw [l, ← nat.iterate.hom, function.comp_app, hn.right] at this,

        specialize hn1 (y - x),
        suffices p : y - x < n,
                have q : ¬ (y - x < n ∧ y - x ≥ n), intro, linarith,
                apply q,
                use p,
                apply hn1,
                exact ⟨by linarith, this⟩,
        have : y - x ≤ y := nat.sub_le y x,
        linarith,
},


-- use n,

-- let initial : two_ptr_state := ⟨ll.head, ll.head, ff, ff⟩,

-- have bruh :
--  nat.iterate ll.two_ptr_step (m-1)  ⟨ll.head, ll.head, ff, ff⟩ 
--  = ⟨nat.iterate ll.next (m-1) ll.head, nat.iterate ll.next (2*(m-1)) ll.head, ff, ff⟩,
-- induction m-1 with d dh,
-- simp [nat.iterate],

-- rw ← nat.iterate.succ,
-- rw function.comp,
-- simp, rw dh,
-- simp [two_ptr_step, if_false],
-- suffices : ¬ (ll.next^[d] ll.head = (ll.next^[2 * d] ll.head)),
-- simp [if_neg this],
-- split,
-- rw ← nat.iterate.succ,

-- have l := nat.iterate.hom ℕ ll.next 2 (2*d),
-- have : d.succ = d + 1, norm_num,
-- rw this,
-- ring,
-- rw ← l,
-- simp,
-- rw ← function.comp.def (ll.next^[2]) (ll.next^[2 * d]) ll.head,
-- rw ← function.comp.def (ll.next^[2 * d]) (ll.next^[2]) ll.head,
-- rw nat.iterate.hom,
-- rw nat.iterate.hom,
-- ring,
end

#check nat.iterate
end cycle_detection

end linked_list