module

public import QuantitativeMaassMovingBroadDeficitV1
public import QuantitativeMaassMovingBroadApproxV1
public import QuantitativeMaassBroadDeficitEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass.Scheduled

/-- Removing the noncuspidal part of actual moving-cutoff cylinder
columns is negligible after any ambient filter with the stated norm bound.
The filter need not commute with the cutoff, wave, or cuspidal projection. -/
theorem moving_filtered_noncuspidal_energy_decay
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬p∣N) (hNp : (N:ZMod p) ≠ 0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (δ P D : ℝ) (hδ : 0 < δ) (hP : 0 ≤ P) (hD : 0 ≤ D)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x)=1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (F : ℝ → AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (V W : ℝ)
    (hF : ∀ᶠ t in atTop, ‖F t‖^2 ≤ Real.exp (V*Strong.strongScale t)) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z, ‖F t (cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))) -
        F t (localCuspidalProjection N hN
          (cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))))‖^2
        ∂quotientMeasure 0)/(t*ε t)) atTop (𝓝 0) := by
  obtain ⟨G,hG,happrox⟩ := movingBroad_global_approximation_decay N δ P D hδ hP hD K hc he hK hm ε hε hp (W+V)
  have hdeficit := moving_broad_cutoff_deficit_energy_decay N p hN hpN hNp a b hab δ P D hδ hP
    G (W+V) hG.le K hc he ε hε hp
  have hlim := (hdeficit.add happrox).const_mul 2
  simp only [add_zero, mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε, eventually_ge_atTop (1:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg (fun _ => sq_nonneg _))) (mul_nonneg (zero_le_one.trans ht) heps.1.le)
  · filter_upwards [hε, eventually_ge_atTop (1:ℝ), hF] with t heps ht hF
    let x := fun z => cutoffTransfer N (movingLowerEdge δ P ε t) D t (movingLowerEdge_pos hδ P ε t) (cylinderAutomorphic (column K hc he ε t z))
    let Q := broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
    let A := ∫ z, ‖actualLVDeficit N p hN hpN a b hab (Strong.deepLVDegree t) (Q (x z))‖^2
      ∂quotientMeasure 0
    let B := ∫ z, ‖Q (x z)-x z‖^2 ∂quotientMeasure 0
    have hA : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
    have hB : 0 ≤ B := integral_nonneg (fun _ => sq_nonneg _)
    have hh := filtered_packet_noncuspidal_integral_le (quotientMeasure 0) N p hN hpN hNp hpres
      a b hab (Strong.deepLVDegree t) Q (F t) x (broadCutoff_column_memLp N (movingLowerEdge δ P ε t) D (movingLowerEdge_pos hδ P ε t) K hc he ε t)
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hF (by positivity : 0 ≤ 2*A+2*B))
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh' (Real.exp_pos _).le) (mul_nonneg (zero_le_one.trans ht) heps.1.le)).trans_eq
    change Real.exp (W*Strong.strongScale t)*(Real.exp (V*Strong.strongScale t)*(2*A+2*B))/(t*ε t) =
      2*(Real.exp ((W+V)*Strong.strongScale t)*A/(t*ε t)+
        Real.exp ((W+V)*Strong.strongScale t)*B/(t*ε t))
    rw [show Real.exp ((W+V)*Strong.strongScale t) =
      Real.exp (W*Strong.strongScale t)*Real.exp (V*Strong.strongScale t) by
        rw [← Real.exp_add]
        congr 1
        ring]
    ring

#print axioms moving_filtered_noncuspidal_energy_decay

end QuantitativeMaass.Scheduled
