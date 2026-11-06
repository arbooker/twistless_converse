module

public import QuantitativeEulerEndpointSharpenCoefficientsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial MeasureTheory
open scoped unitInterval

/-- A single chosen polynomial simultaneously has the explicit degree,
coefficient mass, endpoint, order and integrated-defect bounds. -/
theorem exists_controlled_polynomial_sharpening {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsFiniteMeasure μ] (f : β → I)
    (hf : Measurable (fun x => (f x : ℝ))) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧
      (∑ d∈p.support, |p.coeff d|) ≤ (((16*J^5:ℕ):ℝ)+2)*(3:ℝ)^(16*J^5) ∧ p.eval 0=0 ∧ p.eval 1=1 ∧
      (∀ x : I, 0≤p.eval (x:ℝ) ∧ p.eval (x:ℝ)≤(x:ℝ)) ∧
      (∫ x, p.eval (f x : ℝ)-(p.eval (f x : ℝ))^2 ∂μ)≤4*μ.real Set.univ/(J:ℝ) := by
  obtain ⟨j,hj⟩ := exists_light_band μ (fun x => (f x : ℝ)) hf hJ
  let n := 16*J^5
  have hn : 0<n := by dsimp [n]; positivity
  have hJR : 0<(J:ℝ) := by exact_mod_cast hJ
  refine ⟨sharpen n (bandCenter J j),sharpen_natDegree_le _ _,sharpen_coefficient_mass _ _,sharpen_zero _ _,
    sharpen_one (Nat.ne_of_gt hn) (bandCenter_upper hJ j),sharpen_bounds _ _,?_⟩
  have he : 1/((n:ℝ)*(bandWidth J)^2)=1/(J:ℝ) := by
    dsimp [n,bandWidth]
    push_cast
    field_simp
    ring
  have hh := sharpen_defect_integral μ f hf hn (by positivity : 0≤1/(J:ℝ))
    (bandWidth_pos hJ) (bandCenter_lower hJ j)
  rw [he] at hh
  calc
    _ ≤ (2*(1/(J:ℝ))+1/(J:ℝ))*μ.real Set.univ+
        μ.real {x | (f x : ℝ)∈Set.Icc (bandCenter J j-bandWidth J) (bandCenter J j+bandWidth J)} := hh
    _ ≤ (2*(1/(J:ℝ))+1/(J:ℝ))*μ.real Set.univ+μ.real Set.univ/(J:ℝ) := add_le_add le_rfl hj
    _ = 4*μ.real Set.univ/(J:ℝ) := by ring

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Fully quantitative monotone polynomial sharpening of an actual positive
contraction and its actual finite tracial spectral measure. -/
theorem exists_controlled_operator_sharpening (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧
      (∑ d∈p.support, |p.coeff d|) ≤ (((16*J^5:ℕ):ℝ)+2)*(3:ℝ)^(16*J^5) ∧ p.eval 0=0 ∧ p.eval 1=1 ∧
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
  refine ⟨p,hdeg,hmass,hzero,hone,?_,?_,?_⟩
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

#print axioms exists_controlled_polynomial_sharpening
#print axioms exists_controlled_operator_sharpening
end QuantitativeEulerEndpointBernstein
