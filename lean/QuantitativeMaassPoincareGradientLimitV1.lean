module

public import QuantitativeMaassPoincareDerivativeLimitV1
public import QuantitativeMaassLpLimitRepresentativeV1
public import QuantitativeArithmeticMaassGradientExtensionV1
public import Mathlib.Analysis.Calculus.Rademacher

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential QuantitativeArithmeticMaassGradient

local instance : Measure.IsAddHaarMeasure (volume : Measure Point) := by
  rw [Measure.volume_eq_prod]
  infer_instance

theorem integralCuspChart_representative_coordinates (N : ℕ) (g : gamma N) (z : ℍ) :
    integralCuspChart (representative g) (z.re,z.im)=((g•z).re,(g•z).im) := by
  have h := congruence_pullback_cartesian N (fun Z => (⟨Z.1,Z.2⟩:ℂ)) g (z.re,z.im) z.im_pos
  rw [cartesianLift_positive _ z.im_pos] at h
  exact Prod.ext (congrArg Complex.re h).symm (congrArg Complex.im h).symm

/-- Seed derivative convergence holds simultaneously along almost every orbit,
so the derivatives of the actual periodizations converge almost everywhere. -/
theorem compact_poincare_fderiv_tendsto_ae (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (u : ℕ → SmoothUpperSeed) {L : NNReal} {f : Point → ℂ} (hf : LipschitzWith L f)
    (hus : ∀ n,tsupport (upperFunction (u n).toFun)⊆K)
    (hfs : tsupport (upperFunction f)⊆K)
    (ht : ∀ᵐ Z ∂(volume : Measure Point),Tendsto (fun n => fderiv ℝ (u n).toFun Z)
      atTop (𝓝 (fderiv ℝ f Z))) :
    ∀ᵐ z : ℍ ∂quotientMeasure N,
      Tendsto (fun n => fderiv ℝ (congruencePoincareCartesian N (u n).toFun) (z.re,z.im))
        atTop (𝓝 (fderiv ℝ (congruencePoincareCartesian N f) (z.re,z.im))) := by
  have hdiff : ∀ᵐ Z ∂(volume : Measure Point),DifferentiableAt ℝ f Z := hf.ae_differentiableAt
  have hboth := ae_quotient_orbit_coordinates N
    ((hdiff.and ht).mono (fun Z h _ => h))
  filter_upwards [hboth] with z hz
  apply compact_poincare_fderiv_tendsto N K hK (fun n => (u n).toFun) f hus hfs
    (z.re,z.im) z.im_pos
  · intro n g
    have hp := integralCuspChart_pos (representative g) (z.re,z.im) z.im_pos
    exact ((u n).smooth.contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by simp)
  · intro g
    rw [integralCuspChart_representative_coordinates]
    exact (hz g).1
  · intro g
    rw [integralCuspChart_representative_coordinates]
    exact (hz g).2

/-- The completed quotient gradient is the actual a.e. derivative of the
periodized Lipschitz seed obtained by strong Sobolev approximation. -/
theorem quotientGradient_limit_representative (N : ℕ) (i : Bool)
    (K : Set ℍ) (hK : IsCompact K) (u : ℕ → SmoothUpperSeed)
    {L : NNReal} {f : Point → ℂ} (hf : LipschitzWith L f)
    (hus : ∀ n,tsupport (upperFunction (u n).toFun)⊆K)
    (hfs : tsupport (upperFunction f)⊆K)
    (ht : ∀ᵐ Z ∂(volume : Measure Point),Tendsto (fun n => fderiv ℝ (u n).toFun Z)
      atTop (𝓝 (fderiv ℝ f Z)))
    {U : QuotientEnergySpace N}
    (hU : Tendsto (fun n => smoothEnergyMap N (seedModule (u n))) atTop (𝓝 U)) :
    (quotientGradient N i U : ℍ → ℂ)=ᵐ[quotientMeasure N]
      fun z => (z.im:ℂ)*dir (axis i) (congruencePoincareCartesian N f) (z.re,z.im) := by
  have hL : Tendsto (fun n => seedGradientLp N i (u n)) atTop (𝓝 (quotientGradient N i U)) := by
    have hh := (quotientGradient N i).continuous.tendsto U |>.comp hU
    change Tendsto (fun n => quotientGradient N i (smoothEnergyMap N (seedModule (u n))))
      atTop (𝓝 (quotientGradient N i U)) at hh
    simpa only [smoothEnergyMap_seed,quotientGradient_seed] using hh
  apply lp_limit_ae_eq hL (fun n => (seedGradient_memLp N i (u n)).coeFn_toLp)
  filter_upwards [compact_poincare_fderiv_tendsto_ae N K hK u hf hus hfs ht] with z hz
  have he : Continuous (fun D : Point →L[ℝ] ℂ => (z.im:ℂ)*D (axis i)) := by fun_prop
  exact he.continuousAt.tendsto.comp hz

#print axioms integralCuspChart_representative_coordinates
#print axioms compact_poincare_fderiv_tendsto_ae
#print axioms quotientGradient_limit_representative

end QuantitativeMaass
