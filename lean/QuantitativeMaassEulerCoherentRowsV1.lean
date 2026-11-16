module

public import QuantitativeMaassEulerCoherentReconstructionV1
public import QuantitativeMaassRamifiedResidualZeroV1
public import AsymptoticFiniteBranchRowsV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.EulerHilbert.FullTerminal
open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open AsymptoticFiniteBranch AsymptoticCompactObservationCount
variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

theorem coherent_original_row_zero (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hg : physicalIsometry A hN P e g=
      principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb)
    (hd : ∀ p,p∈simplePrimes N → delta e p=b p*(Real.sqrt p:ℂ))
    (hFE : ∀ q : ℕ,0<q → ∀ z : ℂ,0<z.im →
      FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q z=
        multiplier e q*FinitenessAnalyticReconstruction.twist (principalEulerPhysical b r σ) q
          (-1/((Nat.lcm N (q^2):ℂ)*z)))
    (row : Row N) {s : Set ℍ} (hs : IsCompact s) :
    holomorphicSum (rowExpression hN row e hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+3)) 0
        (physicalIsometry A hN P e g)=0 := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hu := principalEulerWeightedLp_coeFn hN A P' r σ hb
  rw [←hg] at hu
  have hrow : rowOperator hN row e hs P'.epsilon_pos (P'.s+3) 0
      (EulerHilbert.normalized A hN P e g)=0 := by
    cases row with
    | twist q hq =>
      apply AsymptoticTwistObservation.residual_eq_zero N q hN hq hs P'.epsilon_pos
        (P'.s+3) 0 (multiplier e q) (principalEulerPhysical b r σ)
        (principalEulerPhysical_periodic b r σ) _ _ hu
      intro z hz
      simpa only [mul_zero,pow_zero,div_one] using hFE q hq z hz
    | ramified p hp hpN =>
      exact ramified_residual_weightZero_eq_zero p hp.pos hs P'.epsilon_pos (P'.s+3)
        (AsymptoticCylinderRamified.eigenvalue e p) (principalEulerPhysical b r σ)
        (principalEulerPhysical_periodic b r σ)
        (principalEulerPhysical_ramified r σ hb e hd hp hpN) _ hu
  exact (congrArg (fun T => T (EulerHilbert.normalized A hN P e g))
    (cylinder_rowExpression hN row e hs P'.epsilon_pos (P'.s+3) 0)).trans hrow

/-- One actual normalized datum simultaneously satisfies every compact
original twist AND ramified row. All equations come from the Euler input. -/
theorem original_all_observation_rows (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      physicalIsometry A hN P e g=
        principalEulerWeightedLp hN A (AsymptoticReconstructedCount.parameters A P) r σ hb ∧
      ∀ (row : Row N) (s : Set ℍ) (hs : IsCompact s),
        holomorphicSum (rowExpression hN row e hs
          (AsymptoticReconstructedCount.parameters A P).epsilon_pos
          ((AsymptoticReconstructedCount.parameters A P).s+3)) 0
            (physicalIsometry A hN P e g)=0 := by
  obtain ⟨e,g,hg,hd,hFE⟩ := EulerHilbert.original_coherent_physical_range A hN P r σ hb
  exact ⟨e,g,hg,fun row _ hs => coherent_original_row_zero A hN P r σ hb e g hg hd hFE row hs⟩

#print axioms coherent_original_row_zero
#print axioms original_all_observation_rows
end QuantitativeMaass.EulerHilbert.FullTerminal
