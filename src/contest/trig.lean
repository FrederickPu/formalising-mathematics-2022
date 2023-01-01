import tactic
import data.real.basic
import data.real.sqrt

noncomputable theory
open_locale classical

constant sin: ℝ → ℝ
constant cos: ℝ → ℝ
constant tan: ℝ → ℝ
constant sec: ℝ → ℝ
constant csc: ℝ → ℝ

constant π : ℝ

variables (x y : ℝ)
axiom pythag : (sin x)^2 + (cos x)^2 = 1

axiom sinpi : sin π = 0
axiom sinpihalf : sin (π/2) = 1
axiom sinpithird : sin (π/3) = (real.sqrt 3) / 2
axiom cospithird : cos (π/3) = (1:ℚ) / 2


axiom sums : sin (x + y) = sin x * cos y + cos x * sin y
axiom diffs : sin (x - y) = sin x * cos y - cos x * sin y
axiom sumc : cos (x + y) = cos x * cos y - sin x * sin y
axiom diffc : cos (x - y) = cos x * cos y + sin x * sin y

axiom tandef : tan x = sin x/ cos x
axiom secdef : sec x = 1 / cos x
axiom cscdef : csc x = 1 / sin x

lemma pythagr (h : cos x ≠ 0) : (tan x)^2 + 1 = 1/ (cos x)^2 :=
begin
rw tandef, field_simp, rw pythag,
end
lemma pythagr' (h : cos x ≠ 0) : (tan x)^2 + 1 = sec x ^ 2 :=
begin
rw tandef, rw secdef, field_simp, rw pythag,
end
lemma pythag1 :  (cos x)^2 + (sin x)^2 = 1:=
begin
rw ← pythag x, ring,
end
lemma pythag2 :  (sin x)^2 = 1-(cos x)^2 :=
begin
rw ← pythag x, ring,
end
lemma pythag3 :  (cos x)^2 = 1-(sin x)^2 :=
begin
rw ← pythag x, ring,
end
theorem sumofcubes : x^3 +y^3 = (x+y)*(x^2 - x*y + y^2) :=
begin
ring,
end
theorem diffofcubes : x^3 -y^3 = (x-y)*(x^2 + x*y + y^2) :=
begin
ring,
end
theorem sin2angle : sin (2*x) = 2 * sin x * cos x :=
begin
have : 2*x = x + x, ring,
rw [this, sums],
ring,
end

theorem cos2angle : cos (2*x) = cos x ^2 - sin x^2 :=
begin
have : 2*x = x + x, ring,
rw [this, sumc],
ring,
end

lemma cos2anglec : cos (2*x) = 2*cos x ^2 - 1 :=
begin
rw cos2angle,
rw pythag2,
ring,
end

lemma cos2angles : cos (2*x) = 1- 2*sin x^2 :=
begin
rw cos2angle,
rw pythag3,
ring,
end

-- simplfiying expressions using ring tactic
-- step 1: set thing equal to random constant
-- step 2: keep manipulating lHS
-- step 3: copy paste simplified LHS into RHS as goal

-- in this case, the 1 gets replaced with sin x * 3 - 4 * sin x ^ 3
example : sin (3*x) = 1 :=
begin
have : 3*x = x + 2*x := by ring,
rw [this, sums],
rw [sin2angle, cos2angle],
ring_exp,
rw pythag3,
ring_exp,
end

theorem sin3angle : sin (3*x) = 3*sin x - 4 * sin x ^ 3 :=
begin
have : 3*x = x + 2*x := by ring,
rw [this, sums],
rw [sin2angle, cos2angle],
ring_exp,
rw pythag3,
ring_exp,
end

example : (cos x)^6  + (sin x)^6 = 1 - 3 *(sin x)^2 + 3 *(sin x)^4 :=
begin
have := sumofcubes ((cos x)^2) ((sin x)^2),
  rw pythag1 at this, ring_exp at this,

  rw this,
  have : (cos x)^4 = ((cos x)^2)^2 := by ring,
  rw this,
  rw pythag3 x,
  ring_exp,
end

lemma join (h : x ≠ 0): 1/x - x = (1 - x^2) / x :=
begin
field_simp, ring,
end

example (h : sin x ≠ 0) (l : cos x ≠ 0) : 
(sec x - cos x) * (csc x - sin x) = tan x / (1 + (tan x)^2):=
begin
  rw cscdef, rw secdef,
  have h1 : 1 / (cos x) - cos x = (sin x)^2 / (cos x),
    rw join, rw ← pythag2, exact l,
  have h2 : 1 / (sin x) - sin x = (cos x)^2 / (sin x),
    rw join, rw ← pythag3, exact h,

  rw [h1, h2], field_simp,
  rw add_comm,
  rw pythagr x, field_simp,
  rw tandef, field_simp, ring,

  exact l,
end

example (h : sin x ≠ 0) (l : cos x ≠ 0) : 
(sec x)^6 -(tan x)^6 = 1 + 3 *(tan x)^2 * (sec x)^2:=
begin
  have l1 : sec x ^ 6 = (sec x ^ 2 ) ^ 3 := by ring,
  have l2 : sec x ^ 2 = 1/cos x^2 := by {rw secdef, field_simp},

  rw [l1, l2, ← pythagr x],
  ring, exact l,
end

example (h : sin x ≠ 0) (l : cos x ≠ 0) :
(sin x)^2=(1-(cos (2*x))) /2 := 
begin
have l : 2*x = x+x, ring,
rw l,
rw sumc,
have dilone : sin x* sin x = (sin x)^2, ring,
rw dilone, 
rw pythag2, ring, 
end

example (h : tan x ≠ 0) (h2 : tan y ≠ 0) (h3 : tan x + tan y ≠ 0):
(tan x + tan y)/(1 /(tan x) + 1/(tan y)) = (tan x)*(tan y) :=
begin
have dillone : 1 / (tan x) + 1 / (tan y) = (tan x + tan y)/(tan x * tan y),
field_simp, ring,
rw dillone,
field_simp, ring,
end

example (h :  2 * cos x + 1 ≠ 0) (h1 : cos (2 * x) ≠ 0):
(sin x + sin (2*x) + sin (3*x)) / (cos x + cos (2*x)+ cos (3*x)) = tan (2*x) :=
begin
  have l : x = 2*x - x, ring,
  have l2 : 3*x = 2*x + x, ring,
  rw [congr_arg sin l, congr_arg cos l, l2],

  rw [sums, sumc, diffs, diffc],
  rw tandef,
  have : sin (2 * x) * cos x - cos (2 * x) * sin x + sin (2 * x) + (sin (2 * x) * cos x + cos (2 * x) * sin x) = (2 * cos x + 1) * sin (2 * x),
  ring_nf,
  rw this,

  have : cos (2 * x) * cos x + sin (2 * x) * sin x + cos (2 * x) + (cos (2 * x) * cos x - sin (2 * x) * sin x) = (2 * cos x + 1) * cos (2 * x),
  ring,
  rw this,
  field_simp, ring,
end

lemma mul_sin : (sin (x + y))*(sin (x - y)) = (sin x)^2 - (sin y)^2 :=
begin
rw [sums, diffs],
ring,
rw [pythag3, pythag3 x],
ring,
end

example (h : (sin x - cos x) ≠ 0)
: (sin x ^ 3 - cos x ^ 3) / (sin x - cos x) = (2 + sin (2*x)) / 2 :=
begin
have : sin x ^ 3 - cos x ^ 3 = (sin x - cos x)*(1+ sin x * cos x),
rw diffofcubes,
rw [add_comm, ← add_assoc],
rw [add_comm (cos x ^2) (sin x ^ 2), pythag],

rw [sin2angle, this],
field_simp, ring,
end

example : sin (4*x) = 4*cos x * sin x*(2 * cos x ^2 -1) :=
begin
have : 2*(2*x) = 4*x, ring,
rw ← this,
rw sin2angle,
rw [cos2anglec, sin2angle],
ring,
end

example : 
cos x ^ 2 * cos y ^ 2 + sin x ^2 * sin y ^ 2 
+ sin x ^ 2 * cos y ^ 2 + sin y ^ 2* cos x ^ 2  = 1 :=
begin
suffices : (sin x ^ 2 + cos x ^ 2) * (sin y ^ 2 + cos y ^ 2) = 1,
linarith,

simp [pythag],
end

example (h : cos x ≠ 0) (h1 : cos y ≠ 0):
sec x ^ 2 - sec y ^ 2 = tan x ^ 2 - tan y ^ 2 :=
begin
  rw [← pythagr' x, ← pythagr' y],
  ring,

  exact h1, exact h,
end

example (h : sin x ≠ 0) (h1 : cos x ≠ 0):
csc x ^ 2 + sec x ^ 2 = csc x ^2 * sec x ^2 :=
begin
  simp only [secdef, cscdef],
  field_simp,
  rw add_comm,
  rw pythag,
end

example (h : sin x ≠ 0) (h1 : cos x ≠ 0):
(sec x - cos x)*(csc x - sin x) = (tan x)/(1 + tan x ^ 2) :=
begin
rw [add_comm, pythagr],
rw [cscdef, secdef, tandef],
field_simp, ring,

rw pythag2,
ring,

tauto,
end


example :
4*sin x*sin (π/3 + x)* sin (π/3 - x) = 
sin (3*x) :=
begin
rw [mul_assoc, mul_sin],

rw [sin3angle, sinpithird],
norm_num, ring,
end

#check eq.refl

#check true