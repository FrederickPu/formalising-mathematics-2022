import tactic
import set_theory.cardinal

open_locale cardinal

def pfinset (n : ℕ) : set ℕ := {x : ℕ | x < n}
notation `[`n`]` := pfinset n

namespace cardinal

lemma mk_pfin (n : ℕ) : # [n] = ↑n :=
begin
simp [pfinset],
end

end cardinal
-- n choose k
-- the set of subsets of (fin n) of size k
-- Frederick Pu's Finset definition
def set_choose (n k: ℕ) : set (set ℕ)
:= {s : set ℕ | s ⊆ pfinset n ∧ # s = # (fin k)}

lemma sub_of_sub_pred {n : ℕ} {qval : set ℕ}: 
qval ⊆ [n - 1] → qval ⊆ [n] :=
begin
  intro,
  have : [n-1] ⊆ [n],
  intro x,
  simp [pfinset], exact nat.lt_of_lt_pred,
  exact set.subset.trans ᾰ this,
end

namespace equiv

lemma empty_congr : ↥(∅:set ℕ) ≃ fin 0 :=
{
  to_fun := begin
    intro x, cases x,
    exfalso, tauto,
  end,
  inv_fun := begin
    intro x, cases x,
    exfalso,
    exact nat.not_lt_zero x_val x_property,
  end,
  left_inv := begin
    intro x, cases x,
    tauto,
  end,
  right_inv := begin
    intro x, cases x,
    exfalso, exact nat.not_lt_zero x_val x_property,
  end
}
end equiv

example (n k : ℕ) (hnk : n > k) (hk : k > 0):
 ↥(set_choose (n - 1) k) ⊕ ↥(set_choose (n - 1) (k - 1)) ≃ ↥(set_choose n k) :=
{
  to_fun := begin
    intro p, 
    rcases p with ⟨pval, pprop⟩ | ⟨qval, qprop⟩,

    cases pprop,
    have : pval ⊆ [n] := sub_of_sub_pred pprop_left,
    exact ⟨pval, ⟨this, pprop_right⟩⟩,
    
    cases qprop,
    have qsub: qval ⊆ [n] := sub_of_sub_pred qprop_left,
    have : set ℕ := qval ∪ {n-1},
    have : qval ∪ {n-1} ⊆ [n],
    {
      rw pfinset,
      intro x, simp,
      intro p,
      cases p with l r,
      rw l,
      cases n,
      {linarith},
      {simp, exact lt_add_one n},

      simp [set.subset_def] at qsub,
      exact qsub x r,
    },
    have : # ↥ (qval ∪ {n-1}) = ↑k,
    have : # ↥(qval ∪ {n - 1}) = # ↥qval + # ↥{n - 1},
    rw ← cardinal.mk_union_add_mk_inter,
    suffices : # ↥(qval ∩ {n - 1}) = # (fin 0),
    rw this, simp,
    

    have : k = (k-1)+1, cases k, linarith, simp,
    have : (↑k:cardinal) = ↑(k-1)+↑1,
    rw this, simp,

    rw this,
    simp only [← cardinal.mk_pfin],
    rw ← cardinal.mk_union_add_mk_inter,
    -- have := @cardinal.mk_union_add_mk_inter,
    simp [set_choose],
  end
}

example (n k : ℕ): 
# (set_choose (n-1) k) + # (set_choose (n-1) (k-1)) = # (set_choose n k) := 
begin
rw cardinal.add_def,
rw cardinal.mk_congr,

end