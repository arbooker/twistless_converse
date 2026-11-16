module

public import QuantitativeMaassCompactRegularCancellationV1
public import QuantitativeMaassMovingSharpProjectionMainV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticRegularTrace
open AsymptoticClassicalPetersson AsymptoticCompactBranch AsymptoticSectorSigns QuantitativeNewGap
open scoped lp ComplexConjugate FourierTransform SchwartzMap MatrixGroups
namespace QuantitativeMaass.CountingMetric

/-- After inverse-cap and inverse-metric cancellation, the localized
regular diagonal is exactly the original counting coefficient times the
sharp spatial area. Both factors are retained. -/
theorem compact_metricCompression_diagonal_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    (N : ℕ) (g : ι→quotientNormalizerGroup N)
    {δ Y R : ℝ} (hδ : 0<δ) (hY : 0<Y) (hR : 0≤R) {ν : ℕ} (hν : 1≤ν)
    (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)
    (P : ℓ²(Classes (gamma N),ℂ)→L[ℂ]ℓ²(Classes (gamma N),ℂ))
    (a b : ℝ) (ha : 0<a) (hheight : δ*Real.exp (-R)≤a) (w : ℂ) :
    let k := fun z : ℍ =>
      (∑ n ∈ Finset.Icc (-(⌈(ν:ℝ)*R+1⌉₊:ℤ)) (⌈(ν:ℝ)*R+1⌉₊:ℤ),
        LogBands.inverseCoefficient (fun u => Real.log (cappedHeightWeight δ ν u)) n z)*
        (normalizerCoverMetric N g δ ν z:ℂ)⁻¹
    (∫ z in upperRectangle 0 1 a b,
      (k z*conj (k z)*matrix (metricCompression N g hδ hY hν hcover P z) 1 1*w).re)=
      volume.real (upperRectangle 0 1 a b)*(matrix P (classOf (gamma N) 1) (classOf (gamma N) 1)*w).re := by
  intro k
  calc
    _ = ∫ _z in upperRectangle 0 1 a b,
        (matrix P (classOf (gamma N) 1) (classOf (gamma N) 1)*w).re := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (upperRectangle_measurable 0 1 a b),
        upperRectangle_ae_strip a b ha] with z hz hstrip
      have hh := compact_metricCompression_matrix N g hδ hY hR hν hcover P z 1 1
        (by simpa only [one_smul] using hstrip) (by simpa only [one_smul] using hstrip)
        (by simpa only [one_smul] using hheight.trans hz.2.1)
        (by simpa only [one_smul] using hheight.trans hz.2.1)
      dsimp only at hh
      simp only [one_smul] at hh
      change (k z*conj (k z)*matrix (metricCompression N g hδ hY hν hcover P z) 1 1*w).re=_
      rw [show k z*conj (k z)*matrix (metricCompression N g hδ hY hν hcover P z) 1 1=
        matrix P (classOf (gamma N) 1) (classOf (gamma N) 1) from hh]
    _ = _ := by rw [setIntegral_const]; rfl

#print axioms compact_metricCompression_diagonal_integral
end QuantitativeMaass.CountingMetric

namespace QuantitativeMaass.AdmissibleScalarCover
open Scheduled
local instance (N : ℕ) [NeZero N] : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _

/-- The literal regular counterpart of the compact canonical subtraction
has the same sharp main term as the physical trace comparison. -/
theorem moving_regular_canonical_main {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (cover : AdmissibleScalarCover N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (e : Sector N) (C : ℝ) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t : ℝ) :
    let R := C*radius ε t
    let k := fun z : ℍ =>
      (∑ n ∈ Finset.Icc (-(⌈(ν:ℝ)*R+1⌉₊:ℤ)) (⌈(ν:ℝ)*R+1⌉₊:ℤ),
        LogBands.inverseCoefficient (fun u => Real.log (cappedHeightWeight δ ν u)) n z)*
        (normalizerCoverMetric N cover.family δ ν z:ℂ)⁻¹
    (∫ z in cutoffRectangle (movingLowerEdge δ C ε t) t,
      (k z*conj (k z)*matrix (cover.regularProjection hδ hν e z) 1 1*
        windowIdentityContribution K hc (radius ε t) (radius_pos ε t) t (t+ε t)).re)=
      movingSharpSectorProjectionMain N hN.1 e δ C K hc ε t := by
  exact CountingMetric.compact_metricCompression_diagonal_integral N cover.family hδ cover.height_pos
    (mul_nonneg hC (radius_pos ε t).le) hν cover.covers (countingSectorSpace N hN.1 e).starProjection
    (movingLowerEdge δ C ε t) (Real.exp (Strong.strongScale t/2)) (movingLowerEdge_pos hδ C ε t)
    le_rfl _

#print axioms moving_regular_canonical_main
end QuantitativeMaass.AdmissibleScalarCover
