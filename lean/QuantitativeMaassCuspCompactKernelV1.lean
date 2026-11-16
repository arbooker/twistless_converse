module

public import QuantitativeMaassCuspKernelBoundV1
public import QuantitativeMaassIntegratedWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups

namespace QuantitativeMaass

local instance (N : ℕ) : DecidableEq (gamma N) := Classical.decEq _

/-- All terms from a cusp chart inject into one fixed finite full-level
orbit set in standard coordinates. This gives an absolute majorant without
assuming invariance of the congruence subgroup under cusp conjugation. -/
theorem radialNonidentity_chart_finite_majorant (N : ℕ) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o z : ℍ) (L : ℝ) (hz : dist z o≤L) :
    ‖radialNonidentity N g (A•z)‖≤
      ∑ γ∈(diagonalOrbitSet 1 o (R+2*L)).erase 1,‖g (Real.cosh (dist (γ•z) z))‖ := by
  classical
  let S := (diagonalOrbitSet N (A•z) R).erase 1
  let T := (diagonalOrbitSet 1 o (R+2*L)).erase 1
  let φ := cuspConjugateFull N A
  have he : radialNonidentity N g (A•z)=∑ γ∈S,g (Real.cosh (dist (γ•(A•z)) (A•z))) := by
    rw [radialNonidentity_eq_finite N g R hR hs (A•z) (A•z) 0 (by simp)]
    apply Finset.sum_congr
    · ext γ
      simp only [S,mul_zero,add_zero,Finset.mem_erase]
    · intro γ _
      rfl
  have hsub : S.image φ⊆T := by
    intro q hq
    obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hq
    have hm := Finset.mem_erase.mp hγ
    have hn : φ γ≠1 := by
      intro hh
      exact hm.1 (cuspConjugateFull_injective N A (hh.trans (cuspConjugateFull_one N A).symm))
    apply Finset.mem_erase.mpr
    refine ⟨hn,?_⟩
    apply displacement_in_diagonalOrbitSet 1 o z L R hz
    rw [cuspConjugateFull_displacement]
    exact (mem_diagonalOrbitSet N (A•z) R γ).mp hm.2
  rw [he]
  calc
    _ ≤ ∑ γ∈S,‖g (Real.cosh (dist (γ•(A•z)) (A•z)))‖ := norm_sum_le _ _
    _ = ∑ γ∈S,‖g (Real.cosh (dist (φ γ•z) z))‖ := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [cuspConjugateFull_displacement]
    _ = ∑ γ∈S.image φ,‖g (Real.cosh (dist (γ•z) z))‖ := by
      rw [Finset.sum_image (fun _ _ _ _ hh => cuspConjugateFull_injective N A hh)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)

/-- Fixed compact-chart integration costs one geometric constant, uniformly
in the level and integral chart; the kernel amplitude is retained linearly. -/
theorem radialNonidentity_chart_integral_bound (N : ℕ) (A : SL(2,ℤ))
    (o : ℍ) (L R : ℝ) (hR : 0≤R) (g : ℝ → ℂ) (hg : ContinuousOn g (Ici 1))
    (hs : Function.support g⊆Iic (Real.cosh R)) (C : ℝ) (hC : 0≤C)
    (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d)) :
    (∫ z in Metric.closedBall o L,‖radialNonidentity N g (A•z)‖)≤
      (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L):ℝ)*C*
        (Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (R+2*L))) := by
  classical
  let S := (diagonalOrbitSet 1 o (R+2*L)).erase 1
  let E := Real.pi*(volume.real (Metric.closedBall o L)+hyperbolicSublevelConstant o L (R+2*L))
  have hE : 0≤E := by
    have hh := hyperbolicSublevelConstant_nonneg o L (R+2*L)
    dsimp only [E]
    positivity
  have hi : IntegrableOn (fun z : ℍ => radialNonidentity N g (A•z)) (Metric.closedBall o L) :=
    ((radialNonidentity_continuous N g hg R hR hs).comp
      (Isometry.of_dist_eq (fun x y => integral_action_dist A x y)).continuous).continuousOn.integrableOn_compact
      (isCompact_closedBall o L)
  have heach (γ : gamma 1) (hγ : γ∈S) :=
    diagonalOrbitSet_profile_integral_bound 1 o L (R+2*L) γ
      (Finset.mem_erase.mp hγ).2 (Finset.mem_erase.mp hγ).1 g hg C hC hb
  have his (γ : gamma 1) (hγ : γ∈S) :
      IntegrableOn (fun z : ℍ => ‖g (Real.cosh (dist (γ•z) z))‖) (Metric.closedBall o L) :=
    (heach γ hγ).1.norm
  calc
    _ ≤ ∫ z in Metric.closedBall o L,∑ γ∈S,‖g (Real.cosh (dist (γ•z) z))‖ := by
      apply integral_mono_ae hi.norm (integrable_finsetSum S his)
      filter_upwards [ae_restrict_mem ((isCompact_closedBall o L).measurableSet)] with z hz
      exact radialNonidentity_chart_finite_majorant N A g R hR hs o z L hz
    _ = ∑ γ∈S,∫ z in Metric.closedBall o L,‖g (Real.cosh (dist (γ•z) z))‖ := integral_finsetSum S his
    _ ≤ ∑ _γ∈S,C*E := Finset.sum_le_sum (fun γ hγ => (heach γ hγ).2)
    _ = (S.card:ℝ)*(C*E) := by simp
    _ ≤ (QuantitativeArithmeticMaassOverlap.energyMultiplicity o 0 (R+2*L):ℝ)*(C*E) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hE)
      exact_mod_cast (Finset.card_erase_le.trans (diagonalOrbitSet_card_bound 1 o (R+2*L)))
    _ = _ := by dsimp only [E];ring

#print axioms radialNonidentity_chart_finite_majorant
#print axioms radialNonidentity_chart_integral_bound

end QuantitativeMaass
