module

public import QuantitativeMaassReflectedCorrespondenceKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- Sum all actual reflected terms on the centre ball, using finite
propagation and the explicit lattice multiplicity. -/
theorem radialReflectedIntegralKernel_integral_bound (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (B : ℝ) (hB : 0<B) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (o : ℍ) (L R : ℝ)
    (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (fun z => radialPoincareKernel N g z (positiveIntegralGL M hM • (J•z))) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖(fun z => radialPoincareKernel N g z (positiveIntegralGL M hM • (J•z))) z‖)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o+2*Real.log (2*B)))) := by
  classical
  let S := diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o)
  let E := Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o+2*Real.log (2*B)))
  have hE : 0≤E := by
    have hh := reflectedSublevelConstant_nonneg o L (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o+2*Real.log (2*B))
    dsimp only [E]
    positivity
  have hi : IntegrableOn ((fun z => radialPoincareKernel N g z (positiveIntegralGL M hM • (J•z)))) (Metric.closedBall o L) :=
    ((radialPoincareKernel_joint_continuous_physical N g hg R hR hs).comp
      (continuous_id.prodMk ((continuous_const_smul (positiveIntegralGL M hM)).comp (continuous_const_smul J)))).continuousOn.integrableOn_compact (isCompact_closedBall o L)
  have heach (γ : gamma N) (hγ : γ∈S) :=
    congruence_product_reflected_profile_integral_bound N o L (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o) B hB γ
      hγ M hM hentry g hg C hC hb
  have his (γ : gamma N) (hγ : γ∈S) :
      IntegrableOn (fun z : ℍ => ‖g (Real.cosh (dist (γ•(positiveIntegralGL M hM • (J•z))) z))‖) (Metric.closedBall o L) :=
    (heach γ hγ).1.norm
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L,∑ γ∈S,‖g (Real.cosh (dist (γ•(positiveIntegralGL M hM • (J•z))) z))‖ := by
      apply integral_mono_ae hi.norm (integrable_finsetSum S his)
      filter_upwards [ae_restrict_mem ((isCompact_closedBall o L).measurableSet)] with z hz
      change ‖radialPoincareKernel N g z (positiveIntegralGL M hM • (J•z))‖≤_
      rw [radialReflectedIntegralKernel_eq_finite N M hM g R hR hs o z L hz]
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr
      · ext γ
        rfl
      · intro γ _
        rfl
    _ = ∑ γ∈S,∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ•(positiveIntegralGL M hM • (J•z))) z))‖ :=
      integral_finsetSum S his
    _ ≤ ∑ _γ∈S,C*E := Finset.sum_le_sum (fun γ hγ => (heach γ hγ).2)
    _ = (S.card:ℝ)*(C*E) := by simp
    _ ≤ (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o):ℝ)*(C*E) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hE)
      exact_mod_cast (diagonalOrbitSet_all_card_bound N o (R+2*L+dist (positiveIntegralGL M hM • (J•o)) o))
    _ = _ := by dsimp only [E];ring

#print axioms radialReflectedIntegralKernel_integral_bound

end QuantitativeMaass
