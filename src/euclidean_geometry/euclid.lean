import algebra.group.defs
import data.real.basic
import data.complex.basic
-- type class formalism of euclid's axioms for planar geometry

structure euclidean_geometry 
(M point lineseg line circle : Type) [add_semigroup M] [linear_order M] :=
(dist : point → point → M)
(angle : point → point → point → M)
(right_angle : M)
(post1 : point → point → lineseg) -- 1st posulate
(post2 : lineseg → line)
(post3 : point → M → circle)

(congr : (point × point × point) → (point × point × point) → Prop)
(trans (T T1 T2: point × point × point) : 
congr T T1 → congr T1 T2 → congr T T2)
(refl (T : point × point × point) : congr T T)

(oncircle : point → circle → Prop)
(online : point → line → Prop)
(onlineseg : point → lineseg → Prop)

(post5 (A B : point) (a b : line) : 
online A a → online B b →  ∃ C, online C a ∧ angle C A B < right_angle →
∃ C₁, online C₁ a ∧ online C₁ b ∧ onlineseg C (post1 A C₁))

(ax1 (p : point) (l₀ : lineseg): onlineseg p l₀ → online p (post2 l₀)) -- the whole is greater than the part
(ax2 (a b c : point) : onlineseg b (post1 a c) → dist a b + dist b c = dist a c) -- 
(ax3 (p C : point) (m : M) : oncircle p (post3 C m) ↔ dist p C = m) -- we can use the circle axiom to prove dist a b = dist b a

(pasch1 (a b c d : point): onlineseg b (post1 a c) → onlineseg c (post1 b d) → onlineseg b (post1 a d))
(pasch2 (A B C: point) (a : line) (hᵢ : ∃ a₀ : point, online a₀ a ∧ onlineseg a₀ (post1 A B)):
∃ a₁ : point, online a₁ a ∧  ¬ (onlineseg a₁ (post1 A B)) →
 ∃ b₀ : point, onlineseg b₀ (post1 B C) ∨ onlineseg b₀ (post1 A C))
-- note that betweeness can be encoded by the line-segement primitive
-- c is between a and b ↔ c is on linesegment a b
