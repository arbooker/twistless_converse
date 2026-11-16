module

public import QuantitativeMaassCompactCanonicalMainV1
public import QuantitativeMaassMajorantSharpProjectionMainV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticRegularTrace
open AsymptoticClassicalPetersson AsymptoticCompactBranch AsymptoticSectorSigns QuantitativeNewGap
open scoped lp ComplexConjugate FourierTransform SchwartzMap MatrixGroups
namespace QuantitativeMaass.AdmissibleScalarCover
open Scheduled
local instance (N : ℕ) [NeZero N] : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _

/-- The literal regular counterpart of the compact canonical subtraction
has the same sharp main term as the physical trace comparison. -/
theorem enlarged_regular_canonical_main {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
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
        windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re)=
      enlargedSharpSectorProjectionMain N hN.1 e δ C K hc ε t := by
  exact CountingMetric.compact_metricCompression_diagonal_integral N cover.family hδ cover.height_pos
    (mul_nonneg hC (radius_pos ε t).le) hν cover.covers (countingSectorSpace N hN.1 e).starProjection
    (movingLowerEdge δ C ε t) (Real.exp (Strong.strongScale t/2)) (movingLowerEdge_pos hδ C ε t)
    le_rfl _

/-- The literal regular counterpart of the compact canonical subtraction
has the same sharp main term as the physical trace comparison. -/
theorem originalMajorant_regular_canonical_main {N : ℕ} [NeZero N] {hN : GridAdmissibleGap.Admissible N}
    (cover : AdmissibleScalarCover N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (e : Sector N) (C : ℝ) (hC : 0≤C)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (t : ℝ) :
    let R := C*radius ε t
    let k := fun z : ℍ =>
      (∑ n ∈ Finset.Icc (-(⌈(ν:ℝ)*R+1⌉₊:ℤ)) (⌈(ν:ℝ)*R+1⌉₊:ℤ),
        LogBands.inverseCoefficient (fun u => Real.log (cappedHeightWeight δ ν u)) n z)*
        (normalizerCoverMetric N cover.family δ ν z:ℂ)⁻¹
    (QuantitativeNinaMaass.windowEnergyDenominator K ε t)⁻¹^2 *
    (∫ z in cutoffRectangle (movingLowerEdge δ C ε t) t,
      (k z*conj (k z)*matrix (cover.regularProjection hδ hν e z) 1 1*
        windowIdentityContribution K hc (radius ε t) (radius_pos ε t)
        (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).re)=
      originalMajorantSharpSectorProjectionMain N hN.1 e δ C K hc ε t := by
  dsimp only [originalMajorantSharpSectorProjectionMain]
  rw [enlarged_regular_canonical_main cover hδ hν e C hC K hc ε t]

#print axioms enlarged_regular_canonical_main
#print axioms originalMajorant_regular_canonical_main
end QuantitativeMaass.AdmissibleScalarCover
