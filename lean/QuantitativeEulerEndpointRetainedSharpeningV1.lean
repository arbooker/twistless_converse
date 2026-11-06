module

public import QuantitativeEulerEndpointSharpenControlledV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial MeasureTheory
open scoped unitInterval

/-- Scalar bounds retained for the same polynomial in every representation. -/
def ScalarSharpening (p : ℝ[X]) : Prop :=
  p.eval 0=0 ∧ p.eval 1=1 ∧ ∀ x : I, 0≤p.eval (x:ℝ) ∧ p.eval (x:ℝ)≤(x:ℝ)

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Fully quantitative monotone polynomial sharpening of an actual positive
contraction and its actual finite tracial spectral measure. -/
theorem exists_controlled_operator_sharpening_scalar (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧
      (∑ d∈p.support, |p.coeff d|) ≤ (((16*J^5:ℕ):ℝ)+2)*(3:ℝ)^(16*J^5) ∧ ScalarSharpening p ∧
      0≤aeval A p ∧ aeval A p≤A ∧
      τ (aeval A p-(aeval A p)^2)≤4*τ 1/(J:ℝ) := by
  have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA0
  have hn : ‖A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1
  have hspec (x : ℝ) (hx : x∈spectrum ℝ A) : x∈Set.Icc (0:ℝ) 1 := by
    refine ⟨spectrum_nonneg_of_nonneg hA0 hx,?_⟩
    exact (le_abs_self x).trans ((quasispectrum.norm_le_norm_of_mem
      (spectrum_subset_quasispectrum ℝ A hx)).trans hn)
  let μ := QuantitativeTracialSpectralMeasure.measure τ hτ A hA
  let f : spectrum ℝ A → I := fun x => ⟨x.val,hspec x.val x.property⟩
  obtain ⟨p,hdeg,hmass,hzero,hone,hbounds,hdef⟩ := exists_controlled_polynomial_sharpening μ f
    (show Measurable (fun x => (f x : ℝ)) from measurable_subtype_coe) hJ
  refine ⟨p,hdeg,hmass,⟨hzero,hone,hbounds⟩,?_,?_,?_⟩
  · rw [← cfc_polynomial p A hA]
    exact cfc_nonneg (fun x hx => (hbounds ⟨x,hspec x hx⟩).1)
  · have hh := cfc_mono (a := A) (f := p.eval) (g := fun x : ℝ => x)
      (fun x hx => (hbounds ⟨x,hspec x hx⟩).2) p.continuous.continuousOn continuous_id.continuousOn
    rwa [cfc_polynomial p A hA,cfc_id' ℝ A hA] at hh
  · have hi := QuantitativeTracialSpectralMeasure.integral_cfc τ hτ A hA
      (p-p^2).eval (p-p^2).continuous.continuousOn
    rw [cfc_polynomial (p-p^2) A hA,map_sub,map_pow] at hi
    simp only [eval_sub,eval_pow] at hi
    change (∫ x : spectrum ℝ A, p.eval (x:ℝ)-(p.eval (x:ℝ))^2 ∂μ) ≤ _ at hdef
    rw [hi,QuantitativeTracialSpectralMeasure.measure_real_univ τ hτ A hA] at hdef
    exact hdef

theorem scalar_sharpening_order {p : ℝ[X]} (hp : ScalarSharpening p)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) : 0≤aeval A p ∧ aeval A p≤A := by
  have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA0
  have hn : ‖A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1
  have hspec (x : ℝ) (hx : x∈spectrum ℝ A) : x∈Set.Icc (0:ℝ) 1 := by
    refine ⟨spectrum_nonneg_of_nonneg hA0 hx,?_⟩
    exact (le_abs_self x).trans ((quasispectrum.norm_le_norm_of_mem
      (spectrum_subset_quasispectrum ℝ A hx)).trans hn)
  constructor
  · rw [←cfc_polynomial p A hA]
    exact cfc_nonneg (fun x hx => (hp.2.2 ⟨x,hspec x hx⟩).1)
  · have hh := cfc_mono (a:=A) (f:=p.eval) (g:=fun x : ℝ => x)
      (fun x hx => (hp.2.2 ⟨x,hspec x hx⟩).2) p.continuous.continuousOn continuous_id.continuousOn
    rwa [cfc_polynomial p A hA,cfc_id' ℝ A hA] at hh

#print axioms scalar_sharpening_order
#print axioms exists_controlled_operator_sharpening_scalar
end QuantitativeEulerEndpointBernstein
