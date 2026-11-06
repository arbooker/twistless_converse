module

public import FinitenessAllLevelFormalAnalyticV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCertificateBoundary FinitenessAllLevelReconstruction
  FinitenessAllLevelGoodTrace FinitenessAllLevelGlobalHeight FinitenessAllLevelBoundaryGeometry
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction SpanningIntegerRows

variable {N Q p : ℕ} {hQ : 0 < Q}

def initialOperator (a : ℝ) (z : ℂ) : space (radius a) →L[ℂ] ℂ := by
  classical
  exact if hz : Function.Periodic.qParam 1 z ∈ Metric.closedBall (0 : ℂ) (radius a) then
    (ContinuousMap.evalCLM ℂ ⟨Function.Periodic.qParam 1 z, hz⟩).comp (space (radius a)).subtypeL
  else 0

theorem initialOperator_apply (a : ℝ) (z : ℂ) (F : space (radius a)) :
    initialOperator a z F = lift F z := by
  unfold initialOperator lift extend
  split <;> rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def rowOperator (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (G : ℂ → X →L[ℂ] ℂ)
    (j : Fin Q) (z : ℂ) : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q → X →L[ℂ] ℂ
  | .inl i =>
      (χ i.val.1 / (((Real.sqrt (Nat.lcm N (i.val.1 ^ 2)) : ℝ) : ℂ) *
        (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q)) ^ (2 * m)) •
      ∑ v ∈ (Finset.range i.val.1).filter (fun v => Nat.Coprime v i.val.1),
        G (-1 / ((Nat.lcm N (i.val.1 ^ 2) : ℕ) *
          (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q)) + (v : ℂ) / i.val.1)
  | .inr i =>
      firstMultiplier (fun _ => lam) m i.1.val •
        G ((i.1.val : ℂ) * (z + ((i.2 : ℂ) - (j.val : ℂ)) / Q)) -
      (i.1.val : ℂ) ^ (2 * m) •
        G ((i.1.val : ℂ) ^ 2 * (z + ((i.2 : ℂ) - (j.val : ℂ)) / Q))

theorem rowOperator_apply (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (G : ℂ → X →L[ℂ] ℂ)
    (j : Fin Q) (z : ℂ) (i : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q) (x : X) :
    rowOperator χ m lam G j z i x =
      twoDilationRow (fun w => G w x) (2 * m) χ (firstMultiplier (fun _ => lam) m)
        (fun q => (q : ℂ) ^ (2 * m)) j z i := by
  cases i <;> simp [rowOperator, twoDilationRow, frickeRow, twist]

def stepOperator (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (G : ℂ → X →L[ℂ] ℂ) (z : ℂ) : X →L[ℂ] ℂ :=
  let w := Function.Periodic.qParam 1 z
  let j := selector Q hQ w
  ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) •
    rowOperator χ m lam G j (line (coordinate w) z.im) i

theorem stepOperator_apply (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    (G : ℂ → X →L[ℂ] ℂ) (z : ℂ) (x : X) :
    stepOperator A χ m lam G z x = step A χ m lam (fun w => G w x) z := by
  simp [stepOperator, step, rowOperator_apply]

def iterateOperator (A : Certificate N {p} Q hQ) (a : ℝ) (χ : ℕ → ℂ) (m : ℕ)
    (lam : ℂ) : ℕ → ℂ → space (radius a) →L[ℂ] ℂ
  | 0 => initialOperator a
  | n + 1 => fun z => if a ≤ z.im then initialOperator a z else
      stepOperator A χ m lam (iterateOperator A a χ m lam n) z

theorem iterateOperator_apply (A : Certificate N {p} Q hQ) (a : ℝ) (χ : ℕ → ℂ) (m : ℕ)
    (lam : ℂ) (n : ℕ) (z : ℂ) (F : space (radius a)) :
    iterateOperator A a χ m lam n z F = iterate A a χ m lam F n z := by
  induction n generalizing z with
  | zero => exact initialOperator_apply a z F
  | succ n ih =>
      by_cases hz : a ≤ z.im
      · simp only [iterateOperator, iterate, ite_eq_left hz, initialOperator_apply]
      · simp only [iterateOperator, iterate, ite_eq_right hz, stepOperator_apply, ih]

/-- Evaluation of formal continuation at any spatial point is an actual
bounded linear functional of the initial Banach-disk input. -/
def formalOperator (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (z : ℂ) : space (radius a) →L[ℂ] ℂ :=
  iterateOperator A a χ m lam (depth A P a z) z

theorem formalOperator_apply (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (z : ℂ) (F : space (radius a)) :
    formalOperator A P a χ m lam z F = formal A P a χ m lam F z :=
  iterateOperator_apply A a χ m lam _ z F

#print axioms rowOperator_apply
#print axioms iterateOperator_apply
#print axioms formalOperator_apply

end FinitenessAllLevelFormalContinuation
