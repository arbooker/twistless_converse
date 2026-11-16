module

public import QuantitativeMaassCorrespondenceKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Integrate the actual off-diagonal radial profile along every nonscalar
congruence-times-integral-matrix branch, including elliptic products. -/
theorem congruence_product_profile_integral_bound (N : ℕ) (o : ℍ) (L D B : ℝ) (hB : 0<B)
    (γ : gamma N) (hγ : γ∈diagonalOrbitSet N o D)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (hne : integralProductNonscalar N M γ)
    (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))‖)≤
      C*(Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (D+2*Real.log (2*B)))) := by
  have hc : Continuous (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))) :=
    hg.comp_continuous (Real.continuous_cosh.comp (((AsymptoticRationalBranches.action_continuous γ.val).comp (continuous_const_smul (positiveIntegralGL M hM))).dist continuous_id))
      (fun _ => Real.one_le_cosh _)
  have hi : IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))) (Metric.closedBall o L) :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall o L)
  obtain ⟨hj,hbound⟩ := congruence_product_inverse_sqrt_integral N o L D B hB γ hγ M hM hentry hne
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L,C*(1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • z)) z)) := by
      apply integral_mono_ae hi.norm (hj.const_mul C)
      filter_upwards [congruence_product_displacement_pos_ae N o L D B hB γ hγ M hM hentry hne] with z hz
      calc
        _ ≤ C/Real.sqrt (Real.sinh (dist (γ • (positiveIntegralGL M hM • z)) z)) := hb _ hz
        _ ≤ C/Real.sqrt (dist (γ • (positiveIntegralGL M hM • z)) z) := div_le_div_of_nonneg_left hC
          (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt (Real.self_le_sinh_iff.mpr hz.le))
        _ = _ := by ring
    _ = C*(∫ z in Metric.closedBall o L,1/Real.sqrt (dist (γ • (positiveIntegralGL M hM • z)) z)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hC

/-- Sum all actual nonscalar correspondence terms on a centre ball.
The orbit and denominator costs of the fixed matrix are explicit. -/
theorem radialIntegralRemainder_integral_bound (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (B : ℝ) (hB : 0<B) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (o : ℍ) (L R : ℝ) (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o L) ∧
    (∫ z in Metric.closedBall o L,‖radialIntegralRemainder N M hM g z‖)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0
        (R+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*C*
      (Real.pi*(volume.real (Metric.closedBall o L)+
        hyperbolicSublevelConstant o L (R+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*B)))) := by
  classical
  let D := R+2*L+dist (positiveIntegralGL M hM • o) o
  let S := (diagonalOrbitSet N o D).filter (integralProductNonscalar N M)
  let E := Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (D+2*Real.log (2*B)))
  have hE : 0≤E := by
    have hh := hyperbolicSublevelConstant_nonneg o L (D+2*Real.log (2*B))
    dsimp only [E]
    positivity
  have heach (γ : gamma N) (hγ : γ∈S) := congruence_product_profile_integral_bound N o L D B hB
    γ (Finset.mem_filter.mp hγ).1 M hM hentry (Finset.mem_filter.mp hγ).2 g hg C hC hb
  have his (γ : gamma N) (hγ : γ∈S) :
      IntegrableOn (fun z : ℍ => g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z)))
        (Metric.closedBall o L) := (heach γ hγ).1
  have hrep : radialIntegralRemainder N M hM g=ᵐ[volume.restrict (Metric.closedBall o L)]
      (fun z => ∑ γ∈S,g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))) := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
    exact radialIntegralRemainder_eq_finite N M hM g R hR hs o z L hz
  have hi : IntegrableOn (radialIntegralRemainder N M hM g) (Metric.closedBall o L) :=
    (integrable_finsetSum S his).congr hrep.symm
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in Metric.closedBall o L,∑ γ∈S,‖g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))‖ := by
      apply integral_mono_ae hi.norm (integrable_finsetSum S (fun γ hγ => (his γ hγ).norm))
      filter_upwards [hrep] with z hz
      rw [hz]
      exact norm_sum_le _ _
    _ = ∑ γ∈S,∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ • (positiveIntegralGL M hM • z)) z))‖ :=
      integral_finsetSum S (fun γ hγ => (his γ hγ).norm)
    _ ≤ ∑ _γ∈S,C*E := Finset.sum_le_sum (fun γ hγ => (heach γ hγ).2)
    _ = (S.card:ℝ)*(C*E) := by simp
    _ ≤ (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 D:ℝ)*(C*E) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hE)
      exact_mod_cast (Finset.card_filter_le _ _).trans (diagonalOrbitSet_card_bound N o D)
    _ = _ := by dsimp only [D,E];ring

/-- The same actual correspondence bound holds for the spectral quotient
measure, by its proved domination by hyperbolic volume. -/
theorem radialIntegralRemainder_quotient_integral_bound (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (B : ℝ) (hB : 0<B) (hentry : ∀ i j,|(M i j:ℝ)|≤B)
    (o : ℍ) (L R : ℝ) (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L,‖radialIntegralRemainder N M hM g z‖ ∂quotientMeasure N)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0
        (R+2*L+dist (positiveIntegralGL M hM • o) o):ℝ)*C*
      (Real.pi*(volume.real (Metric.closedBall o L)+
        hyperbolicSublevelConstant o L (R+2*L+dist (positiveIntegralGL M hM • o) o+2*Real.log (2*B)))) := by
  obtain ⟨hi,hbound⟩ := radialIntegralRemainder_integral_bound N M hM B hB hentry o L R hR g hg hs C hC hb
  exact (integral_mono_measure
    (Measure.restrict_mono_measure (normalized_quotientMeasure_le_volume N) _)
    (Eventually.of_forall (fun z => norm_nonneg _)) hi.norm).trans hbound

#print axioms congruence_product_profile_integral_bound
#print axioms radialIntegralRemainder_integral_bound
#print axioms radialIntegralRemainder_quotient_integral_bound

end QuantitativeMaass
