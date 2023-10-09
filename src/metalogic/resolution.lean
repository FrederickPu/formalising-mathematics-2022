inductive term 
| true : ℕ → term
| nottrue : ℕ → term
structure disjun :=
(term1 : term)
(term2 : term)

structure conj_norm :=
(l : list disjun)

