import tactic
set_option trace.eqn_compiler.elim_match true

structure linked_list :=
(head : ℕ)
(next : ℕ → ℕ)

lemma what (α : Type) (f : α → α) (n : ℕ) : (f ∘ (f^[n])) = (f^[n+1]) :=
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
namespace linked_list
variables (ll : linked_list)

def cycle_at (a : ℕ) := ∃ n : ℕ, ll.next^[n] a = a

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
cases h1 with n hn,
cases h2 with m hm,
use n,

let initial : two_ptr_state := ⟨ll.head, ll.head, ff, ff⟩,

have bruh :
 nat.iterate ll.two_ptr_step (m-1)  ⟨ll.head, ll.head, ff, ff⟩ 
 = ⟨nat.iterate ll.next (m-1) ll.head, nat.iterate ll.next (2*(m-1)) ll.head, ff, ff⟩,
induction m-1 with d dh,
simp [nat.iterate],

rw ← what,
rw function.comp,
simp, rw dh,
simp [two_ptr_step, if_false],
suffices : ¬ (ll.next^[d] ll.head = (ll.next^[2 * d] ll.head)),
simp [if_neg this],
end

example (P : Prop) [decidable P] (a b : ℕ): ¬ P → (ite P a b) = b :=
begin
intro h,
exact if_neg h,
end

#check nat.iterate
end cycle_detection

end linked_list