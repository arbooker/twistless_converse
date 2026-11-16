module

public import QuantitativeMaassBroadDeficitColumnBoundV1
public import QuantitativeMaassDeepLVDeficitScaleV1
public import QuantitativeMaassStrongLocalScaleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology

namespace QuantitativeMaass.Strong

/-- The actual compact broad-deficit energy is negligible after every
fixed strong-scale exponential loss. Only explicit compact-set geometry
is required; there is no spectral-count or trace-asymptotic hypothesis. -/
theorem broadDeficit_compact_weighted_limit
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬p∣N) (hNp : (N:ZMod p) ≠ 0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (o : ℍ) (G H V W : ℝ) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (K : ℝ → Set ℍ) (hK : ∀ t, IsCompact (K t))
    (hball : ∀ᶠ t in atTop, K t ⊆ Metric.closedBall o (H*strongScale t))
    (hvol : ∀ᶠ t in atTop, volume.real (K t) ≤ Real.exp (V*strongScale t))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*
      (∫ z in K t, ‖actualLVDeficit N p hN hpN a b hab (deepLVDegree t)
        (broadAbelColumn N (Real.exp (G*strongScale t)) (Real.exp_pos _) t z)‖^2)/(t*ε t))
      atTop (𝓝 0) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := broadActualDeficit_column_energy_bound o
  let F := 4+4*max 1 (heckeWordErrorGrowth p)+44*|Real.log p|
  have hmain := (deepLV_deficit_decay p ε (W+V+G) hε hp).const_mul (2*A)
  have herr := (deepLV_geometric_decay ε F (W+6*G+30*H) hε hp).const_mul B
  have hlim := hmain.add herr
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hε, eventually_ge_atTop (1:ℝ)] with t he ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg (fun _ => sq_nonneg _))) (by positivity)
  · filter_upwards [hε, eventually_ge_atTop (1:ℝ), hball, hvol,
      exponential_band_width_quarter G hG] with t he ht hball hvol hwidth
    let L := Real.exp (G*strongScale t)
    let d := deepLVDegree t
    have hd : 0 < d := deepLVDegree_pos t
    have hL : 1 ≤ L := hwidth.1
    have hLp : 0 < L := Real.exp_pos _
    have hLt : L ≤ t := by dsimp [L]; linarith [hwidth.2]
    have hs : 0 ≤ strongScale t := sq_nonneg _
    have hD : 0 ≤ lvSphericalDeficit p (2*d) :=
      (finitePlaceSymbol_deficit_bounds p (2*d) (by omega) 0).1.trans
        (finitePlaceSymbol_deficit_bounds p (2*d) (by omega) 0).2
    have hmass : t*L+L^2 ≤ 2*t*L := by nlinarith
    have hb := hbound N p hN hpN hNp a b hab (H*strongScale t) L t hL
      (mul_nonneg hH hs) ht (K t) (hK t) hball d (deepLVDegree_pos t)
    have hmainbound : volume.real (K t)*lvSphericalDeficit p (2*d)*A*(t*L+L^2) ≤
        Real.exp (V*strongScale t)*lvSphericalDeficit p (2*d)*A*(2*t*L) := by
      gcongr
    have hsum := hb.trans (add_le_add hmainbound le_rfl)
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le) (by positivity : 0 ≤ t*ε t)).trans_eq
    dsimp only [F, d, L]
    rw [mul_add, add_div]
    congr 1
    · rw [show Real.exp ((W+V+G)*strongScale t) =
        Real.exp (W*strongScale t)*Real.exp (V*strongScale t)*Real.exp (G*strongScale t) by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring]
      field_simp [show t ≠ 0 by linarith, he.ne']
    · rw [show (Real.exp (G*strongScale t))^6 = Real.exp (6*G*strongScale t) by
        rw [← Real.exp_nat_mul]
        congr 1
        ring]
      rw [show Real.exp ((4+4*max 1 (heckeWordErrorGrowth p)+44*|Real.log p|)*
          (deepLVDegree t:ℝ)+(W+6*G+30*H)*strongScale t) =
          Real.exp (W*strongScale t)*Real.exp (6*G*strongScale t)*
            Real.exp (30*(H*strongScale t)+
              (4+4*max 1 (heckeWordErrorGrowth p)+44*|Real.log p|)*(deepLVDegree t:ℝ)) by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring]
      ring

#print axioms broadDeficit_compact_weighted_limit

end QuantitativeMaass.Strong
