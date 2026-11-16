module

public import QuantitativeMaassMovingNoncuspidalV1
public import QuantitativeArithmeticMaassSharpTransferMassV1
public import QuantitativeArithmeticMaassScheduledTraceCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass.Scheduled

/-- The actual moving-cutoff full-quotient filtered trace may be restricted to cuspidal
input. Both spatial cutoffs stay in their original operator positions. -/
theorem moving_filtered_noncuspidal_trace_decay
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬p∣N) (hNp : (N:ZMod p) ≠ 0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (δ P D : ℝ) (hδ : 0 < δ) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (F : ℝ → AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (V W : ℝ)
    (hF : ∀ᶠ t in atTop, ‖F t‖^2 ≤ Real.exp (V*Strong.strongScale t))
    (O : ℝ → AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hO : ∀ᶠ t in atTop, ‖O t‖ ≤ 1) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (columnLinearTrace (quotientMeasure 0)
        (fun z => F t (cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z)))) (O t) -
       columnLinearTrace (quotientMeasure 0)
        (fun z => F t (localCuspidalProjection N hN
          (cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))))) (O t))/(t*ε t))
      atTop (𝓝 0) := by
  let x := fun t z => cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))
  let c := fun t z => F t (x t z)
  let d := fun t z => F t (localCuspidalProjection N hN (x t z))
  let E := fun t => ∫ z, ‖c t z-d t z‖^2 ∂quotientMeasure 0
  have hmass := movingCutoffTransfer_energy K hc he hK hm ε hε hp hδ P hP
  have hlim := moving_filtered_noncuspidal_energy_decay N p hN hpN hNp hpres a b hab
    δ P D hδ hP hD K hc he hK hm ε hε hp F V (W+(|W|+(|V|+22)+1)) hF
  apply weighted_trace_from_energy ε E _ 1 (|V|+22) W (by norm_num) (by positivity)
    (hε.mono (fun _ h => h.1)) hp
    (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) hlim
  filter_upwards [hmass,hF,hO,hε,eventually_gt_atTop (0:ℝ)] with t hm hFt hOt heps ht
  have hx : MemLp (x t) 2 (quotientMeasure 0) := broadCutoff_column_memLp N (movingLowerEdge δ P ε t) D (movingLowerEdge_pos hδ P ε t) K hc he ε t
  have hc' : MemLp (c t) 2 (quotientMeasure 0) := hx.continuousLinearMap_comp (F t)
  have hd' : MemLp (d t) 2 (quotientMeasure 0) :=
    (hx.continuousLinearMap_comp (localCuspidalProjection N hN)).continuousLinearMap_comp (F t)
  have hix := (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  have hic := (memLp_two_iff_integrable_sq_norm hc'.aestronglyMeasurable).mp hc'
  have hcmass : (∫ z, ‖c t z‖^2 ∂quotientMeasure 0) ≤ 1*t*Real.exp ((|V|+22)*Strong.strongScale t) := by
    calc
      _ ≤ ∫ z, ‖F t‖^2*‖x t z‖^2 ∂quotientMeasure 0 := by
        apply integral_mono hic (hix.const_mul _)
        intro z
        exact (pow_le_pow_left₀ (norm_nonneg _) ((F t).le_opNorm _) 2).trans_eq (mul_pow _ _ _)
      _ = ‖F t‖^2*(∫ z, ‖x t z‖^2 ∂quotientMeasure 0) := integral_const_mul _ _
      _ ≤ Real.exp (V*Strong.strongScale t)*(Real.exp (22*Strong.strongScale t)*(t*ε t)) :=
        mul_le_mul hFt (hm N D) (integral_nonneg (fun _ => sq_nonneg _)) (Real.exp_pos _).le
      _ ≤ Real.exp (|V| * Strong.strongScale t)*(Real.exp (22*Strong.strongScale t)*t) := by
        apply mul_le_mul
        · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self V) (sq_nonneg _))
        · exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right ht.le heps.2) (Real.exp_pos _).le
        · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg ht.le heps.1.le)
        · positivity
      _ = _ := by rw [add_mul,Real.exp_add]; ring
  let η := Real.exp (-((|W|+(|V|+22)+1)*Strong.strongScale t))
  have hh := columnLinearTrace_column_perturbation (quotientMeasure 0)
    (d t) (c t) hd' hc' (O t) η (Real.exp_pos _)
  rw [abs_sub_comm] at hh
  have heq : (∫ z, ‖d t z-c t z‖^2 ∂quotientMeasure 0) = E t := by
    apply integral_congr_ae
    filter_upwards with z
    rw [norm_sub_rev]
  rw [heq] at hh
  have hsmall := hh.trans (mul_le_of_le_one_left
    (add_nonneg (mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _)))) hOt)
  exact hsmall.trans (add_le_add (mul_le_mul_of_nonneg_left hcmass (Real.exp_pos _).le) le_rfl)

#print axioms moving_filtered_noncuspidal_trace_decay

end QuantitativeMaass.Scheduled
