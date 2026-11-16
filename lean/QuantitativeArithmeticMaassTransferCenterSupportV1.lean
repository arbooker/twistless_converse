module

public import QuantitativeArithmeticMaassCanonicalCutoffTransferV1
public import QuantitativeMaassCylinderKernelSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped ENNReal ContDiff
namespace QuantitativeMaass

/-- A compact restriction of a cylinder column is zero when its centre is
outside the propagated height rectangle. This is equality in local L2. -/
theorem cylinderAbelColumn_local_zero_outside
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (a b : ℝ)
    (hheight : ∀ x∈K, a≤x.im ∧ x.im≤b) (z : ℍ) (hz : z∈strip)
    (hout : z∉upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)) :
    quotientRestriction 0 K hK hK.measurableSet
      (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))=0 := by
  apply Lp.ext
  filter_upwards [cylinderAbelColumn_local_representative F hF R hR hs K hK z,
    ae_restrict_mem hK.measurableSet,Lp.coeFn_zero ℂ 2 (volume.restrict K)] with x hcol hx hzero
  rw [hcol,hzero]
  change radialPoincareKernel 0 (abelProfile F) z x=0
  by_contra hn
  have hn' : radialPoincareKernel 0 (abelProfile F) x z≠0 := by
    rwa [radialPoincareKernel_symm]
  have hh : |Real.log z.im-Real.log x.im|≤R :=
    le_of_not_gt (fun h => hn' (cylinderRadialKernel_log_zero (abelProfile F) R hR
      (abelProfile_support _ _ hs) x z h))
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply hout
  change z.re∈Icc (0:ℝ) 1 ∧ z.im∈Icc _ _
  refine ⟨⟨hz.1,hz.2.le⟩,?_,?_⟩
  · calc
      _ ≤ x.im*Real.exp (-R) := mul_le_mul_of_nonneg_right (hheight x hx).1 (Real.exp_pos _).le
      _ = Real.exp (Real.log x.im-R) := by rw [Real.exp_sub,Real.exp_log x.im_pos,Real.exp_neg]; rfl
      _ ≤ Real.exp (Real.log z.im) := Real.exp_le_exp.mpr (by linarith)
      _ = z.im := Real.exp_log z.im_pos
  · calc
      z.im = Real.exp (Real.log z.im) := (Real.exp_log z.im_pos).symm
      _ ≤ Real.exp (Real.log x.im+R) := Real.exp_le_exp.mpr (by linarith)
      _ = x.im*Real.exp R := by rw [Real.exp_add,Real.exp_log x.im_pos]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hheight x hx).2 (Real.exp_pos _).le

/-- Both sharp and smooth compact cross-quotient transfers have the same
finite region of possible column centres. -/
theorem boundedCrossQuotientLocalization_column_zero_outside (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (a b : ℝ)
    (hheight : ∀ x∈K, a≤x.im ∧ x.im≤b)
    (v : ℍ → ℂ) (hv : AEStronglyMeasurable v (volume.restrict K))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict K, ‖v x‖≤B)
    (z : ℍ) (hz : z∈strip)
    (hout : z∉upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)) :
    boundedCrossQuotientLocalization N 0 K hK v hv hB
      (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))=0 := by
  unfold boundedCrossQuotientLocalization
  simp only [comp_apply,cylinderAbelColumn_local_zero_outside F hF R hR hs K hK a b hheight z hz hout,
    map_zero]

/-- The full quotient integral of any zero-preserving observable of the
transferred column equals a compact physical-area integral. This includes
quadratic traces and spectral-tail energies. -/
theorem boundedCrossQuotientLocalization_column_integral (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (a b : ℝ) (ha : 0<a)
    (hheight : ∀ x∈K, a≤x.im ∧ x.im≤b)
    (v : ℍ → ℂ) (hv : AEStronglyMeasurable v (volume.restrict K))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict K, ‖v x‖≤B)
    (Φ : AutomorphicSpace N → ℝ) (hΦ : Φ 0=0) :
    let c := fun z => boundedCrossQuotientLocalization N 0 K hK v hv hB
      (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))
    (∫ z, Φ (c z) ∂quotientMeasure 0)=
      ∫ z in upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R), Φ (c z) := by
  intro c
  let S := upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)
  have hS : MeasurableSet S := upperRectangle_measurable _ _ _ _
  have hstrip : ∀ᵐ z ∂quotientMeasure 0, z∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  calc
    _ = ∫ z, S.indicator (fun z => Φ (c z)) z ∂quotientMeasure 0 := by
      apply integral_congr_ae
      filter_upwards [hstrip] with z hz
      by_cases hzS : z∈S
      · rw [Set.indicator_of_mem hzS]
      · rw [Set.indicator_of_notMem hzS]
        have hc : c z=0 := boundedCrossQuotientLocalization_column_zero_outside N F hF R hR hs
          K hK a b hheight v hv hB z hz hzS
        rw [hc,hΦ]
    _ = _ := by
      rw [integral_indicator hS]
      change (∫ z, Φ (c z) ∂(quotientMeasure 0).restrict S)=_
      rw [cylinder_rectangle_measure _ _ (mul_pos ha (Real.exp_pos _))]

/-- Compact transfer makes the full family of cylinder columns genuinely
square-integrable. This justifies the global quadratic traces. -/
theorem boundedCrossQuotientLocalization_column_memLp (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (a b : ℝ) (ha : 0<a)
    (hheight : ∀ x∈K, a≤x.im ∧ x.im≤b)
    (v : ℍ → ℂ) (hv : AEStronglyMeasurable v (volume.restrict K))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict K, ‖v x‖≤B) :
    MemLp (fun z => boundedCrossQuotientLocalization N 0 K hK v hv hB
      (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))) 2 (quotientMeasure 0) := by
  let c := fun z => boundedCrossQuotientLocalization N 0 K hK v hv hB
    (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))
  let S := upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R)
  have hS : IsCompact S := upperRectangle_compact 0 1 _ _ (mul_pos ha (Real.exp_pos _))
  have hc : Continuous c := (boundedCrossQuotientLocalization N 0 K hK v hv hB).continuous.comp
    (cylinderAutomorphic.continuous.comp (cylinderAbelColumn_continuous F hF R hR hs))
  have hlocal : MemLp c 2 (volume.restrict S) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      ((hc.norm.pow 2).continuousOn.integrableOn_compact hS)
  have hlocalq : MemLp c 2 ((quotientMeasure 0).restrict S) := by
    rw [cylinder_rectangle_measure _ _ (mul_pos ha (Real.exp_pos _))]
    exact hlocal
  have hind : MemLp (S.indicator c) 2 (quotientMeasure 0) :=
    (memLp_indicator_iff_restrict (f := c) (p := 2) (μ := quotientMeasure 0) hS.measurableSet).mpr hlocalq
  change MemLp c 2 (quotientMeasure 0)
  apply (memLp_congr_ae (f := S.indicator c) (g := c) ?_).mp hind
  have hstrip : ∀ᵐ z ∂quotientMeasure 0,z∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  filter_upwards [hstrip] with z hz
  by_cases hzS : z∈S
  · rw [Set.indicator_of_mem hzS]
  · rw [Set.indicator_of_notMem hzS]
    exact (boundedCrossQuotientLocalization_column_zero_outside N F hF R hR hs
      K hK a b hheight v hv hB z hz hzS).symm

#print axioms boundedCrossQuotientLocalization_column_memLp

#print axioms cylinderAbelColumn_local_zero_outside
#print axioms boundedCrossQuotientLocalization_column_zero_outside
#print axioms boundedCrossQuotientLocalization_column_integral
end QuantitativeMaass
