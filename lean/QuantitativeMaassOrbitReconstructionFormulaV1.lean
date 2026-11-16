module

public import QuantitativeMaassCountingCapLiftV1
public import AsymptoticWeightedFEV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticCertificateOperators (lowCell lowStrip highStrip amplitude)
open AsymptoticRegularCertificate AsymptoticWeightedBranches
open AsymptoticRegularFoldedLow (Space)
namespace QuantitativeMaass.CountingMetric
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A)

theorem regular_lowPart_section {t : ℕ} (ht : 1≤t) (z : ℍ) (F : ℂ→ℂ)
    (u : Space) (hu : ∀ a,u a=stripSection P.ε t 0 F (a • z))
    (v : Index A) (a : AsymptoticRationalGroup.Group) :
    lowPart A hN P t v z u a=
      lowValue (level_pos A hN v) (inputShift A v) (outputShift A v)
        P.ε P.ρ (lowCell A P.ε v) t 0 F (a • z) := by
  unfold lowPart AsymptoticRegularFoldedLow.operator
  rw [tsum_apply_coordinate _ (Summable.of_norm
    (AsymptoticRegularFoldedLow.term_norm_summable _ _ _ _ _ _ _ _ _ ht z))]
  unfold lowValue
  apply tsum_congr
  intro n
  simp only [AsymptoticRegularFoldedLow.term,AsymptoticOrbitBranch.operator_apply,hu,
    mul_smul,AsymptoticRationalBranches.fold_action,levelQ_cast,inputShiftQ_cast,outputShiftQ_cast,
    Nat.mul_zero,AsymptoticHyperbolicSlash.phase,pow_zero,mul_one]

theorem regular_terminalPart_section {t : ℕ} (ht : 2≤t) (z : ℍ) (F : ℂ→ℂ)
    (u : Space) (hu : ∀ a,u a=stripSection P.ε t 0 F (a • z))
    (v : Index A) (a : AsymptoticRationalGroup.Group) :
    terminalPart A hN P ht v z u a=
      terminalValue (level_pos A hN v) (inputShift A v) (outputShift A v)
        P.ε (lowCell A P.ε v) t 0 F (a • z) := by
  unfold terminalPart AsymptoticRegularFoldedTerminal.operator
  rw [tsum_apply_coordinate _ (Summable.of_norm
    (AsymptoticRegularFoldedTerminal.term_norm_summable _ _ _ _ _ _ _ _ _ _ ht z))]
  unfold terminalValue
  apply tsum_congr
  intro n
  simp only [AsymptoticRegularFoldedTerminal.term,AsymptoticOrbitBranch.operator_apply,hu,
    mul_smul,AsymptoticRationalBranches.fold_action,levelQ_cast,inputShiftQ_cast,outputShiftQ_cast,
    Nat.mul_zero,AsymptoticHyperbolicSlash.phase,pow_zero,mul_one]

/-- The regular all-integer reconstruction equals the pointwise weighted
certificate formula on a genuine orbit section. -/
theorem regular_reconstruction_section (χ : ℕ→ℂ) {t : ℕ} (ht : 2≤t) (z : ℍ) (F : ℂ→ℂ)
    (u : Space) (hu : ∀ a,u a=stripSection P.ε t 0 F (a • z))
    (a : AsymptoticRationalGroup.Group) :
    (low A hN P χ t z u+terminal A hN P χ ht z u) a=
      AsymptoticWeightedFE.reconstructionValue A hN P χ t 0 F (a • z) := by
  change (lp.evalCLM ℂ (fun _ : AsymptoticRationalGroup.Group => ℂ) 2 a)
    ((∑ v : Index A,amplitude A χ v • lowPart A hN P t v z) u+
      (∑ v : Index A,amplitude A χ v • terminalPart A hN P ht v z) u)=_
  simp only [_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,smul_eq_mul]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  change amplitude A χ v*lowPart A hN P t v z u a+
    amplitude A χ v*terminalPart A hN P ht v z u a=_
  rw [regular_lowPart_section A hN P (by omega) z F u hu,
    regular_terminalPart_section A hN P ht z F u hu,mul_add]

#print axioms regular_lowPart_section
#print axioms regular_terminalPart_section
#print axioms regular_reconstruction_section
end QuantitativeMaass.CountingMetric
