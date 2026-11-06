module

public import QuantitativeSpectralCutV1
public import AsymptoticRegularPolarV1
public import AsymptoticPolarSubgroupSupportV1
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace QuantitativeSpectralCutRegularity

open MeasureTheory ContinuousLinearMap QuantitativeSpectralCut
open AsymptoticRegularTrace AsymptoticFunctionalCalculus AsymptoticPolarIsometry
open AsymptoticSubgroupSupport
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

omit [Group G] [Countable G] in
private theorem positivePart_eq_value (A : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    positivePart A = value (fun r : ℝ => r⁺) A := by
  exact positivePart_eq_cfc A

private theorem continuous_positivePart : Continuous (fun r : ℝ => r⁺) := by
  simpa only [posPart_def, id_eq] using (continuous_id.max continuous_const : Continuous (fun r : ℝ => max r 0))

/-- Positive-part functional calculus preserves the actual measurable
covariant operator family. -/
theorem positivePart_regular (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hc : Covariant A)
    (hsa : ∀ x, IsSelfAdjoint (A x)) (M : ℝ) (hM : ∀ x, ‖A x‖ ≤ M) :
    (∀ g h, Measurable (fun x => matrix (positivePart (A x)) g h)) ∧ Covariant (fun x => positivePart (A x)) := by
  simp only [positivePart_eq_value]
  exact cfc_regular A hm hc hsa M hM _ continuous_positivePart

/-- Zero-threshold spectral projection regularity follows from the polar
support projection, not from an assumed measurable Borel calculus. -/
theorem high_regular (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hc : Covariant A)
    (hsa : ∀ x, IsSelfAdjoint (A x)) (M : ℝ) (hM : ∀ x, ‖A x‖ ≤ M) :
    (∀ g h, Measurable (fun x => matrix (high (A x)).starProjection g h)) ∧
      Covariant (fun x => (high (A x)).starProjection) := by
  have hp := positivePart_regular A hm hc hsa M hM
  have hv := polar_regular (fun x => positivePart (A x)) hp.1 hp.2 M
    (fun x => (positivePart_norm_le (A x)).trans (hM x))
  have hm' := matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hv.1) hv.1
  have hc' := covariant_comp _ _ (covariant_adjoint _ hv.2) hv.2
  simpa only [polar_gram, high, low, positivePart] using And.intro hm' hc'

omit [Countable G] in
/-- Spectral cuts preserve subgroup support. This is the exact algebraic
integrality needed before processing the next fresh prime. -/
theorem high_supported (S : Subgroup G) (A : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hA : Supported S A) (hsa : IsSelfAdjoint A) :
    Supported S (high A).starProjection := by
  have hp : Supported S (positivePart A) := by
    rw [positivePart_eq_value]
    exact supported_cfc S A hA hsa _ continuous_positivePart
  exact supported_kernelComplement S (positivePart A) hp

omit [Countable G] in
/-- Shifting the threshold preserves subgroup support as well. -/
theorem highAt_supported (S : Subgroup G) (A : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hA : Supported S A) (hsa : IsSelfAdjoint A) (a : ℝ) :
    Supported S (highAt A a).starProjection := by
  apply high_supported S _ _ (shifted_selfAdjoint A hsa a)
  apply supported_sub S _ _ hA
  exact supported_smul S _ (supported_one S) (a : ℂ)

/-- Arbitrary fixed-threshold spectral projections are regular. -/
theorem highAt_regular (A : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (A x) g h)) (hc : Covariant A)
    (hsa : ∀ x, IsSelfAdjoint (A x)) (M : ℝ) (hM : ∀ x, ‖A x‖ ≤ M) (a : ℝ) :
    (∀ g h, Measurable (fun x => matrix (highAt (A x) a).starProjection g h)) ∧
      Covariant (fun x => (highAt (A x) a).starProjection) := by
  let B := fun x => A x - a • (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  have hmB : ∀ g h, Measurable (fun x => matrix (B x) g h) := by
    apply matrix_sub_measurable _ _ hm
    intro g h
    exact measurable_const
  have hcB : Covariant B := by
    apply covariant_sub _ _ hc
    change Covariant (fun _ : α => a • (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)))
    exact covariant_smul (a : ℂ) _ covariant_one
  have hsaB (x : α) : IsSelfAdjoint (B x) :=
    shifted_selfAdjoint (A x) (hsa x) a
  have hnorm (x : α) : ‖B x‖ ≤ M + |a| := by
    apply (norm_sub_le _ _).trans
    apply add_le_add (hM x)
    rw [norm_smul, Real.norm_eq_abs]
    have hn : ‖(1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact (mul_le_mul_of_nonneg_left hn (abs_nonneg a)).trans_eq (mul_one _)
  exact high_regular B hmB hcB hsaB (M+|a|) hnorm

#print axioms positivePart_regular
#print axioms high_regular
#print axioms high_supported
#print axioms highAt_supported
#print axioms highAt_regular

end QuantitativeSpectralCutRegularity
