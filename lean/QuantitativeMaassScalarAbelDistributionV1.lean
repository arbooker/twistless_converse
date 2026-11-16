module

public import QuantitativeMaassScalarRadialBoundV1
public import QuantitativeMaassAbelDistributionMomentsV1
public import QuantitativeMaassPositiveTimeAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

theorem scalarPositiveTest_scaledSub (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (φ ψ : PositiveSmoothTest) (c : ℝ) :
    scalarPositiveAbel f x (positiveSmoothTestToAbel (c • φ-ψ))=
      c • scalarPositiveAbel f x (positiveSmoothTestToAbel φ)-
        scalarPositiveAbel f x (positiveSmoothTestToAbel ψ) := by
  rw [scalarPositiveAbel_congr f x _
    ((positiveSmoothTestToAbel φ).scaledSub (positiveSmoothTestToAbel ψ) c) ?_]
  · exact scalarPositiveAbel_scaledSub f hf x _ _ c
  · funext t
    change ((c*φ t-ψ t:ℝ):ℂ)=(c:ℂ)*(φ t:ℂ)-(ψ t:ℂ)
    push_cast
    rfl

/-- The scalar Abel distribution defined by the literal hyperbolic integral.
Its moment bounds below are obtained from compact local bounds of f. -/
def scalarAbelDistribution (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ) :
    PositiveSmoothTest →ₗ[ℝ] ℂ where
  toFun φ := scalarPositiveAbel f x (positiveSmoothTestToAbel φ)
  map_add' φ ψ := by
    have hz : scalarPositiveAbel f x (positiveSmoothTestToAbel 0)=0 := by
      simpa only [one_smul,sub_self] using scalarPositiveTest_scaledSub f hf x 0 0 1
    have hn : scalarPositiveAbel f x (positiveSmoothTestToAbel (-ψ))=
        -scalarPositiveAbel f x (positiveSmoothTestToAbel ψ) := by
      simpa only [zero_smul,zero_sub,hz] using scalarPositiveTest_scaledSub f hf x 0 ψ 0
    simpa only [one_smul,sub_neg_eq_add,hn] using scalarPositiveTest_scaledSub f hf x φ (-ψ) 1
  map_smul' c φ := by
    have hz : scalarPositiveAbel f x (positiveSmoothTestToAbel 0)=0 := by
      simpa only [one_smul,sub_self] using scalarPositiveTest_scaledSub f hf x 0 0 1
    simpa only [hz,sub_zero,RingHom.id_apply] using! scalarPositiveTest_scaledSub f hf x φ 0 c

theorem scalarAbelDistribution_norm_common (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (φ : PositiveSmoothTest) (δ R C B : ℝ) (hδ : 0<δ) (hR : 0≤R) (hB : 0≤B)
    (hs : tsupport φ ⊆ Icc δ R) (hb : ∀ t,‖positiveSmoothTestDeriv φ t‖≤C)
    (hfB : ∀ y ∈ Metric.closedBall x R,‖f y‖≤B) :
    ‖scalarAbelDistribution f hf x φ‖≤(B*positiveTimeNormConstant δ R)*C := by
  apply scalarPositiveAbel_norm_common f hf x (positiveSmoothTestToAbel φ) δ R C B hδ hR hB
  · intro t ht
    apply hs
    apply subset_tsupport
    intro hz
    exact ht (by change (φ t:ℂ)=0; rw [hz,Complex.ofReal_zero])
  · intro t
    have he : deriv (positiveSmoothTestToAbel φ).toFun t=
        ((positiveSmoothTestDeriv φ t:ℝ):ℂ) := by
      rw [positiveSmoothTestDeriv_apply]
      exact ((φ.contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv
    rw [he,Complex.norm_real]
    exact hb t
  · exact hfB

theorem scalarAbelDistribution_moments (f : ℍ → ℂ) (hf : Continuous f) (x : ℍ)
    (φ : PositiveSmoothTest) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n,
      ‖scalarAbelDistribution f hf x (positiveTestPower n φ)‖≤C*R^n ∧
      ‖scalarAbelDistribution f hf x (positiveSmoothTestDeriv (positiveTestPower n φ))‖≤C*R^n := by
  obtain ⟨C,R,hC,hR,hb⟩ := positiveTestPower_exists_two_derivative_bound φ
  let I := positiveSmoothTestInterval φ
  obtain ⟨B,hB,hfB⟩ := continuous_ball_norm_bound f hf x I.right
  let K := B*positiveTimeNormConstant I.left I.right
  have hK : 0≤K := mul_nonneg hB (positiveTimeNormConstant_nonneg _ _ I.left_pos)
  refine ⟨K*C,R,mul_nonneg hK hC,hR,?_⟩
  intro n
  have hs : tsupport (positiveTestPower n φ) ⊆ Icc I.left I.right :=
    (positiveTestPower_tsupport_subset n φ).trans I.subset
  have hs' := (positiveSmoothTestDeriv_tsupport_subset (positiveTestPower n φ)).trans hs
  constructor
  · calc
      _ ≤ K*(C*R^n) := scalarAbelDistribution_norm_common f hf x _ I.left I.right (C*R^n) B
        I.left_pos I.right_nonneg hB hs (fun t => (hb n t).2.1) hfB
      _ = _ := by ring
  · calc
      _ ≤ K*(C*R^n) := scalarAbelDistribution_norm_common f hf x _ I.left I.right (C*R^n) B
        I.left_pos I.right_nonneg hB hs' (fun t => (hb n t).2.2) hfB
      _ = _ := by ring

theorem scalarAbelDistribution_equation (u : ℝ×ℝ → ℂ)
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (e : ℂ)
    (he : ∀ y : ℍ,upperLaplacian u y=e*upperFunction u y) (x : ℍ)
    (φ : PositiveSmoothTest) :
    scalarAbelDistribution (upperFunction u) (upperFunction_continuous hu) x
      (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))=
      (1/4-e)*scalarAbelDistribution (upperFunction u) (upperFunction_continuous hu) x φ := by
  let ψ := positiveSmoothTestToAbel φ
  have hh := classical_abel_convolution_equation ψ.lift ψ.lift_smooth ψ.lift_compact
    ψ.lift_real ψ.right ψ.right_nonneg ψ.lift_support u hu e he x
  rw [ψ.lift_second] at hh
  have ht := scalarPositiveAbel_congr (upperFunction u) x _ _ (positiveSmoothTestToAbel_second φ)
  change scalarPositiveAbel (upperFunction u) x _=_
  rw [ht]
  exact hh

#print axioms scalarPositiveTest_scaledSub
#print axioms scalarAbelDistribution
#print axioms scalarAbelDistribution_norm_common
#print axioms scalarAbelDistribution_moments
#print axioms scalarAbelDistribution_equation

end QuantitativeMaass
