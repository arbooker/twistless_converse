module

public import FinitenessPaperConvergenceV1
public import FinitenessPaperMain1V1

set_option autoImplicit false

@[expose] public section

namespace FinitenessPaper

open Asymptotics AsymptoticSectorComparison FinitenessPaperConvergence

/-- The hypotheses defining `E(N,k)` in the introduction of `paper1.tex`.
Convergence means ordinary convergence of Dirichlet partial sums somewhere.
The value at index zero is the zero extension of a positive-index sequence.
The Euler product, bad-prime relations, and entire finite-order functional
equation are the original predicates; no polynomial growth is assumed here. -/
structure IsSolution (N k : ℕ) (f : ℕ → ℂ) : Prop where
  zero : f 0 = 0
  converges : ConvergesSomewhere f
  euler : FinitenessOriginalInput.EulerProduct N f
  bad : FinitenessOriginalInput.BadPrimeConditions N f
  continuation : FinitenessOriginalInput.Continuation N k f

def E (N k : ℕ) : Set (ℕ → ℂ) := {f | IsSolution N k f}

/-- The convergence formulation and the existing analytic input describe
exactly the same sequences, rather than merely bounding a subset. -/
theorem isSolution_iff_original (N k : ℕ) (f : ℕ → ℂ) :
    IsSolution N k f ↔ FinitenessOriginalInput.IsSolution N k f := by
  constructor
  · intro h
    exact { zero := h.zero
            growth := growth_of_convergesSomewhere h.converges
            euler := h.euler
            bad := h.bad
            continuation := h.continuation }
  · intro h
    exact { zero := h.zero
            converges := (convergesSomewhere_iff_growth f).mpr h.growth
            euler := h.euler
            bad := h.bad
            continuation := h.continuation }

theorem E_eq_original (N k : ℕ) : E N k = FinitenessOriginalInput.S N k := by
  ext f
  exact isSolution_iff_original N k f

/-- Theorem 1.1 (`thm:main1`), in the stronger uniform form: one constant
depending only on the admissible level bounds every positive even weight. -/
theorem main1_uniform (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ, 0 < k → Even k →
      (E N k).Finite ∧ (E N k).ncard ≤ C * k := by
  simpa only [E_eq_original] using FinitenessPaperMain1.uniform_bound N hN

/-- Theorem 1.1 (`thm:main1`) with the paper's convergence-somewhere input:
`E(N,k)` is finite at every positive even weight and its count is `O_N(k)`.
Only the level and its admissibility are parameters. -/
theorem main1 (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    (∀ k : ℕ, 0 < k → Even k → (E N k).Finite) ∧
    (fun k : ℕ => ((E N k).ncard : ℝ))
      =O[evenWeights] (fun k : ℕ => (k : ℝ)) := by
  obtain ⟨C, _hC, hbound⟩ := main1_uniform N hN
  refine ⟨fun k hk he => (hbound k hk he).1, ?_⟩
  simpa only [E_eq_original] using FinitenessPaperMain1.count_isBigO N hN

#print axioms isSolution_iff_original
#print axioms E_eq_original
#print axioms main1_uniform
#print axioms main1

end FinitenessPaper
