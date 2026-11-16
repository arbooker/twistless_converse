module

public import QuantitativeMaassQuotientExpressionBaseV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane AsymptoticFiniteBranch ContinuousLinearMap
open scoped InnerProductSpace

namespace QuantitativeMaass

/-- A weight-zero physical branch has its literal pullback representative,
also when the representative is specified only almost everywhere. -/
theorem physical_branch_representative (b : Branch)
    (f : AsymptoticHyperbolicSlash.Space) (φ : ℍ → ℂ)
    (hf : (f : ℍ → ℂ) =ᵐ[volume] φ) :
    (holomorphic b 0 f : ℍ → ℂ) =ᵐ[volume] branchFunction b φ := by
  have hp := (AsymptoticRationalGroup.measurePreserving b.label).quasiMeasurePreserving.ae hf
  filter_upwards [AsymptoticConcreteRationalBranch.operator_coeFn
    b.label b.coefficient b.measurable b.norm_le 0 f,hp] with z hz hpz
  change holomorphic b 0 f z = b.coefficient z*φ (b.label • z)
  rw [show holomorphic b 0 f z =
    b.coefficient z*AsymptoticSlashGauge.phase b.label 0 z*f (b.label • z) from hz]
  have hphase : AsymptoticSlashGauge.phase b.label 0 z=1 := by
    simp only [AsymptoticSlashGauge.phase,AsymptoticHyperbolicSlash.phase,mul_zero,pow_zero]
  rw [hphase,mul_one,hpz]

/-- The physical and function realizations of the same finite expression
agree almost everywhere, without requiring automorphy of individual branches. -/
theorem physical_expression_representative (E : Expression)
    (f : AsymptoticHyperbolicSlash.Space) (φ : ℍ → ℂ)
    (hf : (f : ℍ → ℂ) =ᵐ[volume] φ) :
    (holomorphicSum E 0 f : ℍ → ℂ) =ᵐ[volume] expressionFunction E φ := by
  induction E with
  | nil =>
    simpa only [holomorphicSum,expressionFunction,List.map_nil,List.sum_nil,
      zero_apply,LinearMap.zero_apply] using
      (Lp.coeFn_zero ℂ 2 volume)
  | cons b E ih =>
    have hb := physical_branch_representative b f φ hf
    filter_upwards [hb,ih,Lp.coeFn_add (holomorphic b 0 f) (holomorphicSum E 0 f)]
      with z hbz hez hsum
    change (holomorphic b 0 f+holomorphicSum E 0 f) z =
      branchFunction b φ z+expressionFunction E φ z
    rw [hsum,Pi.add_apply,hbz,hez]

/-- Exact physical pairing formula for a finite common expression. -/
theorem physical_expression_pairing (E : Expression)
    (f g : AsymptoticHyperbolicSlash.Space) (φ ψ : ℍ → ℂ)
    (hf : (f : ℍ → ℂ) =ᵐ[volume] φ) (hg : (g : ℍ → ℂ) =ᵐ[volume] ψ) :
    inner ℂ f (holomorphicSum E 0 g) =
      ∫ z : ℍ, star (φ z)*expressionFunction E ψ z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf,physical_expression_representative E g ψ hg] with z hfz hgz
  rw [hfz,hgz]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

#print axioms physical_branch_representative
#print axioms physical_expression_representative
#print axioms physical_expression_pairing

end QuantitativeMaass
