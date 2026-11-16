module

public import QuantitativeMaassEulerNormalizationV1
public import AsymptoticTwistObservationFormulaV1
public import QuantitativePositiveGramFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane AsymptoticSectorSigns ContinuousLinearMap
open scoped Topology

namespace QuantitativeMaass
namespace EulerHilbert

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- A literal compact twist residual acting on the exact normalized terminal
data. All pullbacks, caps, folds and the Gram normalizer are fixed before r. -/
def residualRow (e : Sector N) (q : ℕ) (hq : 0<q) {s : Set ℍ} (hs : IsCompact s) :=
  (AsymptoticTwistObservation.residual N q hN hq hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (multiplier e q)).comp
      (AsymptoticCylinderLift.lift.toContinuousLinearMap.comp (normalized A hN P e))

/-- The simultaneous kernel condition for every compact original residual
is derived for the actual normalized datum of each original Euler solution. -/
theorem original_normalized_residuals (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ (e : Sector N) (g : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε),
      (AsymptoticCylinderLift.lift (normalized A hN P e g) =ᵐ[volume]
        AsymptoticWeightedBranches.stripSection (AsymptoticReconstructedCount.parameters A P).ε
          ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (principalEulerPhysical b r σ)) ∧
      ∀ (q : ℕ) (hq : 0<q) (s : Set ℍ) (hs : IsCompact s),residualRow A hN P e q hq hs g=0 := by
  obtain ⟨e,g,hg,hFE⟩ := original_normalized_range A hN P r σ hb
  refine ⟨e,g,hg,?_⟩
  intro q hq s hs
  apply AsymptoticTwistObservation.residual_eq_zero N q hN hq hs
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+3) 0 (multiplier e q)
    (principalEulerPhysical b r σ) (principalEulerPhysical_periodic b r σ) _ _ hg
  intro z hz
  simpa only [mul_zero,pow_zero,div_one] using hFE q hq z hz

#print axioms residualRow
#print axioms original_normalized_residuals

end EulerHilbert

/-- A positive finite residual filter fixes a datum annihilated by its rows.
This algebraic fact is applied to the actual original residuals above. -/
theorem gram_filter_fixes {H K ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (s : Finset ι) (B : ι → H →L[ℂ] K) (g : H)
    (hg : ∀ i∈s,B i g=0) (c : ℝ) (d : ℕ) :
    ((1-c • (∑ i∈s,(B i).adjoint.comp (B i)))^d) g=g := by
  have hS : (∑ i∈s,(B i).adjoint.comp (B i)) g=0 := by
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hg i hi,map_zero]
  have hbase : (1-c • (∑ i∈s,(B i).adjoint.comp (B i))) g=g := by
    simp only [sub_apply,one_apply_eq_self,smul_apply,hS,smul_zero,sub_zero]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ',mul_apply_eq_comp,ih,hbase]

#print axioms gram_filter_fixes

end QuantitativeMaass
