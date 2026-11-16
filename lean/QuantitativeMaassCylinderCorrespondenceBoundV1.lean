module

public import QuantitativeMaassCorrespondenceIntegralV1
public import AsymptoticNestedQuotientsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The finite orbit bound also includes the translation cylinder N=0,
by its literal subgroup inclusion in the level-one group. -/
theorem diagonalOrbitSet_all_card_bound (N : ℕ) (o : ℍ) (D : ℝ) :
    (diagonalOrbitSet N o D).card≤QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 D := by
  classical
  let h := gamma_le_of_dvd (one_dvd N)
  let e : gamma N ↪ gamma 1 := ⟨Subgroup.inclusion h,Subgroup.inclusion_injective h⟩
  have hs : (diagonalOrbitSet N o D).map e⊆diagonalOrbitSet 1 o D := by
    intro η hη
    obtain ⟨γ,hγ,rfl⟩ := Finset.mem_map.mp hη
    apply (mem_diagonalOrbitSet 1 o D (e γ)).mpr
    exact (mem_diagonalOrbitSet N o D γ).mp hγ
  calc
    _=((diagonalOrbitSet N o D).map e).card := (Finset.card_map e).symm
    _≤(diagonalOrbitSet 1 o D).card := Finset.card_le_card hs
    _≤_ := diagonalOrbitSet_card_bound 1 o D

/-- The actual nonscalar correspondence bound, now including the cylinder
without a positive-level hypothesis. -/
theorem radialIntegralRemainder_all_integral_bound (N : ℕ)
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
      exact_mod_cast (Finset.card_filter_le _ _).trans (diagonalOrbitSet_all_card_bound N o D)
    _ = _ := by dsimp only [D,E];ring

#print axioms diagonalOrbitSet_all_card_bound
#print axioms radialIntegralRemainder_all_integral_bound

end QuantitativeMaass
