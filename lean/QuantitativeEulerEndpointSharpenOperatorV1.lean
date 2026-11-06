module

public import QuantitativeEulerEndpointSharpenBandsV1
public import QuantitativeTracialSpectralMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial MeasureTheory
open scoped unitInterval

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- A positive contraction can be sharpened by an ACTUAL polynomial whose
operator remains below it. The trace defect has an explicit degree budget;
no polynomial approximation or spectral-distribution premise is assumed. -/
theorem exists_operator_sharpening (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧ p.eval 0=0 ∧ p.eval 1=1 ∧
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
  obtain ⟨p,hdeg,hzero,hone,hbounds,hdef⟩ := exists_polynomial_sharpening μ f
    (show Measurable (fun x => (f x : ℝ)) from measurable_subtype_coe) hJ
  refine ⟨p,hdeg,hzero,hone,?_,?_,?_⟩
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

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
/-- Polynomial sharpening preserves every exact right fixed space.
This algebraic identity also applies to projections onto Euler solutions. -/
theorem polynomial_right_fixed (A E : 𝔄) (hE : A*E=E) (p : ℝ[X]) :
    aeval A p*E = p.eval 1 • E := by
  have hpow (n : ℕ) : A^n*E=E := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,mul_assoc,hE,ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,add_mul,hp,hq,eval_add,add_smul]
  | monomial n r =>
    simp only [aeval_monomial,eval_monomial,one_pow,mul_one,Algebra.smul_def]
    rw [mul_assoc,hpow]

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem polynomial_preserves_fixed (A E : 𝔄) (hE : A*E=E) (p : ℝ[X]) (hp : p.eval 1=1) :
    aeval A p*E=E := by rw [polynomial_right_fixed A E hE p,hp,one_smul]

#print axioms exists_operator_sharpening
#print axioms polynomial_right_fixed
#print axioms polynomial_preserves_fixed
end QuantitativeEulerEndpointBernstein
