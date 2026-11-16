module

public import QuantitativeMaassEulerGradientV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

theorem eulerGradient_tsum {a b : ℕ → ℂ} (ha : Summable a) (hb : Summable b) :
    (∑' n,eulerGradient (a n) (b n))=eulerGradient (∑' n,a n) (∑' n,b n) := by
  let A := ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let B := ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)
  change (∑' n,(A (a n)+B (b n)))=A (∑' n,a n)+B (∑' n,b n)
  rw [(A.summable ha).tsum_add (B.summable hb),←A.map_tsum ha,←B.map_tsum hb]

theorem principalWeightedGradient_bound (b : ℕ → ℂ) (r : ℝ) (j k σ n : ℕ)
    (a : ℝ) (ha : 0<a) (z : ℝ × ℝ) (hz : a≤z.2) :
    ‖eulerGradient
        (((2*Real.pi:ℝ):ℂ)*Complex.I*principalWeightedTerm b r j (k+1) (σ+1) n z)
        (-((2*Real.pi:ℝ):ℂ)*principalWeightedTerm b r (j+1) (k+1) σ n z)‖ ≤
      (4*Real.pi)*(principalMomentMajorant b j (k+1) (2*Real.pi) a n+
        principalMomentMajorant b (j+1) (k+1) (2*Real.pi) a n) := by
  apply (eulerGradient_norm_le _ _).trans
  have hc : ‖((2*Real.pi:ℝ):ℂ)‖=2*Real.pi := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  rw [norm_mul,norm_mul,norm_mul,norm_neg,hc,Complex.norm_I,mul_one]
  have h1 := principalWeightedTerm_bound b r j (k+1) (σ+1) n a ha z hz
  have h2 := principalWeightedTerm_bound b r (j+1) (k+1) σ n a ha z hz
  nlinarith [Real.pi_pos]

/-- The joint derivative of the infinite original-coefficient series follows
from uniform summable derivative bounds on a positive-height half-plane. -/
theorem principalWeightedSeries_hasFDerivAt {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) (z : ℝ × ℝ) (hz : 0<z.2) :
    HasFDerivAt (principalWeightedSeries b r j k σ)
      (eulerGradient
        (((2*Real.pi:ℝ):ℂ)*Complex.I*principalWeightedSeries b r j (k+1) (σ+1) z)
        (-((2*Real.pi:ℝ):ℂ)*principalWeightedSeries b r (j+1) (k+1) σ z)) z := by
  let a := z.2/2
  have ha : 0<a := by dsimp [a]; positivity
  let U := {w : ℝ × ℝ | a<w.2}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_snd
  have hc : IsPreconnected U :=
    ((convex_Ioi a).linear_preimage (LinearMap.snd ℝ ℝ ℝ)).isPreconnected
  have hzU : z∈U := by change z.2/2<z.2; linarith
  have hs := ((principalMomentMajorant_summable hb j (k+1) (2*Real.pi) a (by positivity) ha).add
    (principalMomentMajorant_summable hb (j+1) (k+1) (2*Real.pi) a (by positivity) ha)).mul_left (4*Real.pi)
  have hd := hasFDerivAt_tsum_of_isPreconnected hs hU hc
    (fun n w hw => principalWeightedTerm_hasFDerivAt b r j k σ n w (ha.trans hw))
    (fun n w hw => principalWeightedGradient_bound b r j k σ n a ha w hw.le)
    hzU (principalWeightedTerm_summable hb r j k σ z hz) hzU
  rw [eulerGradient_tsum
    ((principalWeightedTerm_summable hb r j (k+1) (σ+1) z hz).mul_left _)
    ((principalWeightedTerm_summable hb r (j+1) (k+1) σ z hz).mul_left _),
    tsum_mul_left,tsum_mul_left] at hd
  exact hd

#print axioms eulerGradient_tsum
#print axioms principalWeightedGradient_bound
#print axioms principalWeightedSeries_hasFDerivAt

end QuantitativeMaass
