module

public import QuantitativeMaassBroadDeficitScheduleV1
public import QuantitativeMaassBroadCylinderIntegralV1
public import QuantitativeMaassMajorantColumnsV1
public import QuantitativeMaassMovingBroadDeficitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass.Scheduled

/-- The broad deficit estimate allows the lower cutoff to move with the
propagation radius, as required by the physical canonical trace. -/
theorem originalMajorant_broad_cutoff_deficit_energy_decay
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬p∣N) (hNp : (N:ZMod p) ≠ 0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (δ C D : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (G W : ℝ) (hG : 0 ≤ G)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      (∫ z, ‖actualLVDeficit N p hN hpN a b hab (Strong.deepLVDegree t)
        (broadQuotientPacket N (Real.exp (G*Strong.strongScale t)) (Real.exp_pos _) t
          (cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
            (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))))‖^2
        ∂quotientMeasure 0)/(t*ε t)) atTop (𝓝 0) := by
  let lower := fun t => movingLowerEdge δ C ε t
  have hlim := Strong.broadDeficit_compact_weighted_limit N p hN hpN hNp a b hab
    I G 4 4 (W+18) hG (by norm_num) (fun t => cutoffRectangle (lower t) t)
    (fun t => upperRectangle_compact 0 1 (lower t) _ (movingLowerEdge_pos hδ C ε t))
    (movingCutoffRectangle_ball hδ C hC ε hε hp)
    (movingCutoffRectangle_volume hδ C hC ε hε hp) ε (hε.mono (fun _ h => h.1)) hp
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε, eventually_ge_atTop (1:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg (fun _ => sq_nonneg _))) (mul_nonneg (zero_le_one.trans ht) heps.1.le)
  · filter_upwards [hε, eventually_ge_atTop (1:ℝ), originalMajorant_cylinder_scheduled_norm K hc ε hε hp,
      movingMultiplicity_bound hδ C hC ε hε hp] with t heps ht hpacket hmult
    let L := Real.exp (G*Strong.strongScale t)
    let T := actualLVDeficit N p hN hpN a b hab (Strong.deepLVDegree t)
    let E := ∫ w in cutoffRectangle (lower t) t, ‖T (broadAbelColumn N L (Real.exp_pos _) t w)‖^2
    have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
    have hov (z : ℍ) (Γ : Finset (gamma 0))
        (hΓ : ∀ g ∈ Γ, g • z ∈ cutoffRectangle (lower t) t) : Γ.card ≤ movingMultiplicity δ C ε t := by
      apply terminal_strip_overlap_bound 0 (lower t) (movingLowerEdge_pos hδ C ε t) z Γ
      intro g hg
      exact ⟨(hΓ g hg).1.1,(hΓ g hg).1.2,(hΓ g hg).2.1⟩
    have hb := broadCross_cylinder_integral_le N L (Real.exp_pos _) t (cutoffRectangle (lower t) t)
      (upperRectangle_compact 0 1 (lower t) _ (movingLowerEdge_pos hδ C ε t))
      (lower t) (Real.exp (Strong.strongScale t/2)) (movingLowerEdge_pos hδ C ε t)
      (fun _ hz => hz.2) (cutoffSeed (lower t) D t (movingLowerEdge_pos hδ C ε t)) 1 (by norm_num)
      (fun z _ => cutoffSeed_bound (lower t) D t (movingLowerEdge_pos hδ C ε t) z)
      (movingMultiplicity δ C ε t) hov T (actualLVDeficit_selfAdjoint N p hN hpN a b hab _)
      (QuantitativeNinaMaass.originalWindowMajorant K hc ε t) (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t) (QuantitativeNinaMaass.originalWindowMajorant_even K he hc ε t) (QuantitativeNinaMaass.originalWindowMajorant_real K he hc ε t)
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (originalMajorant_support K hc ε t)
    simp only [one_pow, one_mul] at hb
    have hcost : ‖cylinderTimePacket (QuantitativeNinaMaass.originalWindowMajorant K hc ε t) ((QuantitativeNinaMaass.originalWindowMajorant K hc ε t).smooth ⊤)
        (QuantitativeNinaMaass.originalWindowMajorant_compact K hc ε t)‖^2*(movingMultiplicity δ C ε t:ℝ) ≤
        Real.exp (18*Strong.strongScale t) := by
      calc
        _ ≤ Real.exp (Strong.strongScale t)*Real.exp (17*Strong.strongScale t) := by gcongr
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hcost hE)
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb' (Real.exp_pos _).le)
      (mul_nonneg (zero_le_one.trans ht) heps.1.le)).trans_eq
    change Real.exp (W*Strong.strongScale t)*(Real.exp (18*Strong.strongScale t)*E)/(t*ε t) =
      Real.exp ((W+18)*Strong.strongScale t)*E/(t*ε t)
    rw [← mul_assoc, ← Real.exp_add]
    congr 3
    ring

#print axioms originalMajorant_broad_cutoff_deficit_energy_decay

end QuantitativeMaass.Scheduled
