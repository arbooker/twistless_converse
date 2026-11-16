module

public import QuantitativeMaassParityLocalMainV1
public import QuantitativeMaassCuspHeckeIntertwiningV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

/-- The genuine reflection reverses the horizontal cusp coordinate and keeps height. -/
theorem reflection_horocyclePoint (x y : ℝ) (hy : 0<y) :
    J•horocyclePoint x y hy=horocyclePoint (-x) y hy := by
  apply UpperHalfPlane.ext
  rw [coe_J_smul]
  apply Complex.ext <;> simp [horocyclePoint]

/-- Exact cusp-chart reflection, for arbitrary functions and every height. -/
theorem cuspProfile_reflection (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ) (x y : ℝ) :
    cuspProfile N s (fun z => f (J•z)) x y=
      cuspProfile N (reflectedIntegralMatrix s) f (-x) y := by
  by_cases hy : 0<y
  · simp only [cuspProfile,dite_eq_left hy]
    change f (J•(s•horocyclePoint ((N:ℝ)*x) y hy))=
      f (reflectedIntegralMatrix s•horocyclePoint ((N:ℝ)*(-x)) y hy)
    rw [reflectedIntegralMatrix_action,reflection_horocyclePoint]
    simp only [mul_neg,neg_neg]
  · simp only [cuspProfile,dite_eq_right hy]

/-- The literal constant term at the reflected cusp equals the constant term
of the reflected function. Period reversal needs no integrability hypothesis. -/
theorem cuspConstant_reflection (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hinv : ∀ γ : gamma N,∀ z : ℍ,f (γ.val•z)=f z) (y : ℝ) :
    cuspConstant N s (fun z => f (J•z)) y=
      cuspConstant N (reflectedIntegralMatrix s) f y := by
  unfold cuspConstant zeroFourier
  simp_rw [cuspProfile_reflection]
  rw [intervalIntegral.integral_comp_neg (fun x : ℝ => cuspProfile N (reflectedIntegralMatrix s) f x y)]
  simpa using (cuspProfile_periodic N (reflectedIntegralMatrix s) f hinv y).intervalIntegral_add_eq
    (-1) 0

/-- Exact bounded local constant-term intertwining on continuous invariant representatives. -/
theorem cuspConstantLocal_reflection_representative (N : ℕ) (hN : 0<N)
    (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (hf : Continuous f.val) :
    cuspConstantLocal N s a b ha
      (reflectionIsometry N (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))=
      cuspConstantLocal N (reflectedIntegralMatrix s) a b ha
        (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) := by
  rw [reflectionIsometry_apply]
  apply Lp.ext
  have hrf : Continuous (reflectionRepresentative N f).val := hf.comp (continuous_const_smul J)
  filter_upwards [cuspConstantLocal_representative_ae N hN s a b ha (reflectionRepresentative N f) hrf,
    cuspConstantLocal_representative_ae N hN (reflectedIntegralMatrix s) a b ha f hf] with y hy hz
  rw [hy,hz]
  exact cuspConstant_reflection N s f.val f.property.2.1 y

/-- Reflection intertwines the actual logarithmic constant-term maps on the
entire quotient completion, by the proved continuous Poincare-seed density. -/
theorem cuspLogConstant_reflection (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ)
    (f : AutomorphicSpace N) :
    cuspLogConstant N hN s A B (reflectionIsometry N f)=
      cuspLogConstant N hN (reflectedIntegralMatrix s) A B f := by
  have he : (fun f : AutomorphicSpace N => cuspLogConstant N hN s A B (reflectionIsometry N f))=
      fun f => cuspLogConstant N hN (reflectedIntegralMatrix s) A B f := by
    apply (poincareSeedVector_dense N).equalizer
      ((cuspLogConstant N hN s A B).continuous.comp (reflectionIsometry N).continuous)
      (cuspLogConstant N hN (reflectedIntegralMatrix s) A B).continuous
    funext v
    let vf : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
      ⟨_,poincareSeed_representative N v⟩
    have hc : Continuous vf.val := by
      let : ContinuousConstSMul (gamma N) ℍ :=
        ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
      exact poincareSum_continuous (G := gamma N) _ v.compact (upperFunction_continuous v.smooth)
    change localHalfDensity N A B (Nat.cast_pos.mpr hN)
      (cuspConstantLocal N s (Real.exp A) (Real.exp B) (Real.exp_pos A)
        (reflectionIsometry N (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) vf)))=_
    rw [cuspConstantLocal_reflection_representative N hN s _ _ _ vf hc]
    rfl
  exact congrFun he f

/-- The actual reflection preserves the genuine all-cusp subspace. -/
theorem reflectionIsometry_mem_localCuspidalSpace (N : ℕ) (hN : 0<N)
    (f : AutomorphicSpace N) (hf : f∈localCuspidalSpace N hN) :
    reflectionIsometry N f∈localCuspidalSpace N hN := by
  rw [mem_localCuspidalSpace] at hf ⊢
  intro s A B
  rw [cuspLogConstant_reflection]
  exact hf (reflectedIntegralMatrix s) A B

theorem reflectionIsometry_mem_localCuspidalSpace_iff (N : ℕ) (hN : 0<N)
    (f : AutomorphicSpace N) :
    reflectionIsometry N f∈localCuspidalSpace N hN ↔ f∈localCuspidalSpace N hN := by
  constructor
  · intro hf
    have hh := reflectionIsometry_mem_localCuspidalSpace N hN (reflectionIsometry N f) hf
    rwa [reflectionIsometry_involutive] at hh
  · exact reflectionIsometry_mem_localCuspidalSpace N hN f

/-- Both geometric parity projections preserve the actual cusp space. -/
theorem parityProjection_mem_localCuspidalSpace (N : ℕ) (hN : 0<N)
    (σ : ℝ) (f : AutomorphicSpace N) (hf : f∈localCuspidalSpace N hN) :
    parityProjection N σ f∈localCuspidalSpace N hN := by
  rw [parityProjection_apply]
  exact (localCuspidalSpace N hN).smul_mem _ ((localCuspidalSpace N hN).add_mem hf
    ((localCuspidalSpace N hN).smul_mem _ (reflectionIsometry_mem_localCuspidalSpace N hN f hf)))

#print axioms reflection_horocyclePoint
#print axioms cuspProfile_reflection
#print axioms cuspConstant_reflection
#print axioms cuspConstantLocal_reflection_representative
#print axioms cuspLogConstant_reflection
#print axioms reflectionIsometry_mem_localCuspidalSpace
#print axioms reflectionIsometry_mem_localCuspidalSpace_iff
#print axioms parityProjection_mem_localCuspidalSpace

end QuantitativeMaass
