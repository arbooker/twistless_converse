module

public import FinitenessAllLevelIndexedConstraintsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelConstraintLocus

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace FinitenessAllLevelFormalContinuation
  FinitenessAllLevelCauchyConstraints QuantitativeArithmeticRetainedCertificate
  QuantitativeArithmeticRetainedReconstruction FinitenessAnalyticReconstruction

variable {N Q p : ℕ} {hQ : 0 < Q}

def Index.IsSpatial : Index N Q → Prop
  | .euler _ => False
  | _ => True

/-- Each spatial constraint is linear in its initial Banach-disk vector.
The eigenvalue remains a parameter in this linear map. -/
def spatialLinear (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (e : Index N Q) (lam : ℂ) : space (radius a) →ₗ[ℂ] ℂ :=
  let ev := fun z => (formalOperator A P a χ m lam z).toLinearMap
  match e with
  | .cauchy _ w _ hR hRc hw => transformLinear hN hp A P ha hae χ m hR hRc hw lam - ev w
  | .fricke q _ z _ =>
      (∑ j ∈ (Finset.range q).filter (fun j => Nat.Coprime j q), ev (z + (j : ℂ) / q)) -
        (χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * z) ^ (2 * m)) •
          (∑ j ∈ (Finset.range q).filter (fun j => Nat.Coprime j q),
            ev (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * z) + (j : ℂ) / q))
  | .hecke z _ => (∑ j ∈ Finset.range p, ev (z + (j : ℂ) / p)) -
      (firstMultiplier (fun _ => lam) m p • ev ((p : ℂ) * z) -
        (p : ℂ) ^ (2 * m) • ev ((p : ℂ) ^ 2 * z))
  | .euler _ => 0

theorem spatialLinear_apply (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (e : Index N Q) (he : e.IsSpatial) (lam : ℂ) (F : space (radius a)) :
    spatialLinear hN hp A P ha hae χ m e lam F = scalar A P a χ m e (lam, F) := by
  cases e with
  | cauchy c w R hR hRc hw =>
      simp [spatialLinear, scalar, transformLinear, formalOperator_apply]
  | fricke q hq z hz =>
      simp [spatialLinear, scalar, twist, LinearMap.sum_apply, smul_eq_mul, formalOperator_apply]
  | hecke z hz =>
      simp [spatialLinear, scalar, completeTwist, LinearMap.sum_apply, smul_eq_mul, formalOperator_apply]
  | euler e => exact False.elim he

#print axioms spatialLinear_apply

end FinitenessAllLevelConstraintLocus
