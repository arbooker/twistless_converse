module
public import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section
namespace QuantitativeArithmeticSparseElimination

/-- Sparse rows and row-operation coefficients use the same representation. -/
abbrev Row (K : Type*) := List (K × ℕ)

def eval {K : Type*} [CommRing K] (v : ℕ → K) (r : Row K) : K :=
  (r.map fun t => t.1*v t.2).sum

def coefficient {K : Type*} [CommRing K] (r : Row K) (j : ℕ) : K :=
  ((r.filter fun t => t.2=j).map Prod.fst).sum

theorem eval_zero {K : Type*} [CommRing K] (v : ℕ → K) (r : Row K)
    (h : ∀ t ∈ r, v t.2=0) : eval v r=0 := by
  induction r with
  | nil => simp [eval]
  | cons t r ih =>
    have ht := h t (List.mem_cons_self)
    have hr := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
    simpa [eval,ht] using hr

/-- Every row of a certified elimination program vanishes on the original
kernel. A step may use any input row or earlier step; the dependency and
row-identity checks are finite certificate obligations. -/
theorem replay_zero {K : Type*} [CommRing K]
    (inputs steps instructions : ℕ → Row K) (m s : ℕ)
    (v : ℕ → K)
    (hinput : ∀ j, j<m → eval v (inputs j)=0)
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hcheck : ∀ i, i<s → eval v (steps i)=
      eval (fun j => if j<m then eval v (inputs j) else eval v (steps (j-m)))
        (instructions i)) :
    ∀ i, i<s → eval v (steps i)=0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [hcheck i hi]
    apply eval_zero
    intro t ht
    have hb := hbefore i hi t ht
    by_cases hj : t.2<m
    · simp only [ite_eq_left hj]
      exact hinput t.2 hj
    · simp only [ite_eq_right hj]
      exact ih (t.2-m) (by omega) (by omega)

theorem eval_eq_coefficient_mul {K : Type*} [CommRing K]
    (v : ℕ → K) (r : Row K) (j : ℕ)
    (hz : ∀ t ∈ r, t.2≠j → v t.2=0) :
    eval v r=coefficient r j*v j := by
  induction r with
  | nil => simp [eval,coefficient]
  | cons t r ih =>
    have hr := ih (fun u hu => hz u (List.mem_cons_of_mem t hu))
    by_cases ht : t.2=j
    · simpa [eval,coefficient,ht,add_mul] using
        congrArg (fun x : K => t.1*v j+x) hr
    · have hv := hz t List.mem_cons_self ht
      simp [eval,coefficient,ht,hv] at hr ⊢
      exact hr

/-- Back substitution for any sparse triangular system. All repeated
coordinate-by-coordinate zero proofs reduce to this lemma and finite
support/diagonal checks. -/
theorem triangular_zero {K : Type*} [CommRing K] [NoZeroDivisors K]
    (rows : ℕ → Row K) (n : ℕ) (v : ℕ → K)
    (hsupport : ∀ i, i<n → ∀ t ∈ rows i, t.2 ≤ i)
    (hdiag : ∀ i, i<n → coefficient (rows i) i≠0)
    (hrows : ∀ i, i<n → eval v (rows i)=0) :
    ∀ i, i<n → v i=0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have he := eval_eq_coefficient_mul v (rows i) i (by
      intro t ht hne
      have hle := hsupport i hi t ht
      exact ih t.2 (by omega) (by omega))
    have hm : coefficient (rows i) i*v i=0 := he.symm.trans (hrows i hi)
    exact (mul_eq_zero.mp hm).resolve_left (hdiag i hi)

/-- A program ending in a triangular family certifies the original kernel
without exporting intermediate theorems or a separate zero proof per entry. -/
theorem kernel_of_replay {K : Type*} [CommRing K] [NoZeroDivisors K]
    (inputs steps instructions : ℕ → Row K) (m s n : ℕ)
    (output : ℕ → ℕ) (v : ℕ → K)
    (hinput : ∀ j, j<m → eval v (inputs j)=0)
    (hbefore : ∀ i, i<s → ∀ t ∈ instructions i, t.2<m+i)
    (hcheck : ∀ i, i<s → eval v (steps i)=
      eval (fun j => if j<m then eval v (inputs j) else eval v (steps (j-m)))
        (instructions i))
    (houtput : ∀ i, i<n → output i<s)
    (hsupport : ∀ i, i<n → ∀ t ∈ steps (output i), t.2 ≤ i)
    (hdiag : ∀ i, i<n → coefficient (steps (output i)) i≠0) :
    ∀ i, i<n → v i=0 :=
  triangular_zero (fun i => steps (output i)) n v hsupport hdiag
    (fun i hi => replay_zero inputs steps instructions m s v hinput hbefore hcheck
      (output i) (houtput i hi))

#print axioms replay_zero
#print axioms triangular_zero
#print axioms kernel_of_replay
end QuantitativeArithmeticSparseElimination
