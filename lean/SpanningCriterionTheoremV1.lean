module

public import SpanningCriterionSufficiencyV1
public import SpanningCriterionObstructionV1
public import SpanningCriterionScalarExtensionV1
public import SpanningTraceRemovalV1

@[expose] public section

namespace SpanningCriterion

open GridAdmissibleGap SpanningActualKernel SpanningCriterionCharacter
  SpanningCriterionObstruction SpanningCriterionScalarExtension

/-- Necessity of the arithmetic criterion. A failed order supplies an
explicit complex obstruction at a multiple of any proposed spanning length. -/
theorem condition_of_vanishing {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hv : Vanishing N P) : Condition N P := by
  intro s hs hps
  by_contra hnot
  have hbad : s^2 ≤ levelPart N s := Nat.le_of_not_gt hnot
  obtain ⟨Q,hQ,hPQ,hzero⟩ := (vanishing_iff_zero hN P).mp hv
  have hmult : ∀ f : ℤ → ℚ, Augmented N (P : Set ℕ) (Q*s) f → f = 0 := by
    simpa only [Nat.mul_comm s Q] using
      SpanningTraceRemoval.augmented_zero_at_multiples (by omega : 0 < s) hPQ hzero
  have hcomplex := augmented_zero_extend (K:=ℂ) (Nat.mul_pos hQ (by omega)) hmult
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)
  have hζ : IsPrimitiveRoot ζ s := Complex.isPrimitiveRoot_exp s (by omega)
  obtain ⟨hker,hne⟩ := augmented_obstruction hN hQ hs hζ hbad P hP hps
  exact hne (hcomplex _ hker)

/-- The full spanning theorem of `paper3.tex`: the legal primitive and
retained complete rows span at some length if and only if the stated
strict inequality holds at every eligible order greater than two. -/
theorem spanning_iff {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Vanishing N P ↔ ∀ s : ℕ, 2 < s → (∀ p ∈ P, p ∣ s) →
      levelPart N s < s^2 :=
  ⟨condition_of_vanishing hN P hP, vanishing_of_condition hN P hP⟩

#print axioms condition_of_vanishing
#print axioms spanning_iff

end SpanningCriterion
