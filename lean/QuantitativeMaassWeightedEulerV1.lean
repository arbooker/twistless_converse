module

public import QuantitativeMaassEulerHorizontalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Coefficient-weighted actual moments; all real derivatives stay in this family. -/
def principalWeightedTerm (b : ℕ → ℂ) (r : ℝ) (j k σ n : ℕ) (z : ℝ × ℝ) : ℂ :=
  (b (n+1)*((n+1:ℕ):ℂ)^k)*(MaassKBessel.moment j r (2*Real.pi*((n+1:ℕ):ℝ)*z.2):ℂ)*
    eulerParityPhase σ (n+1) z.1

def principalWeightedSeries (b : ℕ → ℂ) (r : ℝ) (j k σ : ℕ) (z : ℝ × ℝ) : ℂ :=
  ∑' n,principalWeightedTerm b r j k σ n z

theorem principalWeightedTerm_bound (b : ℕ → ℂ) (r : ℝ) (j k σ n : ℕ) (a : ℝ) (ha : 0<a)
    (z : ℝ × ℝ) (hz : a≤z.2) :
    ‖principalWeightedTerm b r j k σ n z‖≤2*principalMomentMajorant b j k (2*Real.pi) a n := by
  unfold principalWeightedTerm
  rw [norm_mul,norm_mul,norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_real]
  calc
    _ ≤ ‖b (n+1)‖*((n+1:ℕ):ℝ)^k*‖MaassKBessel.moment j r (2*Real.pi*((n+1:ℕ):ℝ)*z.2)‖*2 := by
      gcongr
      exact eulerParityPhase_norm_le σ (n+1) z.1
    _ ≤ _ := by
      have hh := principalMomentMajorant_bound b j k r (2*Real.pi) a (by positivity) ha n z.2 hz
      simpa only [mul_comm (2:ℝ)] using mul_le_mul_of_nonneg_right hh (by norm_num : (0:ℝ)≤2)

theorem principalWeightedTerm_summable {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) (z : ℝ × ℝ) (hz : 0<z.2) :
    Summable (fun n => principalWeightedTerm b r j k σ n z) := by
  apply Summable.of_norm_bounded
    ((principalMomentMajorant_summable hb j k (2*Real.pi) z.2 (by positivity) hz).mul_left 2)
  intro n
  exact principalWeightedTerm_bound b r j k σ n z.2 hz z le_rfl

theorem principalWeightedTerm_continuousOn (b : ℕ → ℂ) (r : ℝ) (j k σ n : ℕ) :
    ContinuousOn (principalWeightedTerm b r j k σ n) {z : ℝ × ℝ | 0<z.2} := by
  intro z hz
  change 0<z.2 at hz
  have hp : 0<2*Real.pi*((n+1:ℕ):ℝ)*z.2 := by positivity
  have hc := (MaassKBessel.moment_hasDerivAt j r hp).continuousAt.comp (f:=fun w : ℝ × ℝ => 2*Real.pi*((n+1:ℕ):ℝ)*w.2)
    (by fun_prop : ContinuousAt (fun w : ℝ × ℝ => 2*Real.pi*((n+1:ℕ):ℝ)*w.2) z)
  have hm := Complex.continuous_ofReal.continuousAt.comp (f:=fun w : ℝ × ℝ => MaassKBessel.moment j r (2*Real.pi*((n+1:ℕ):ℝ)*w.2)) hc
  exact ((continuousAt_const.mul hm).mul
    ((eulerParityPhase_continuous σ (n+1)).continuousAt.comp (f:=Prod.fst) (continuous_fst.continuousAt (x:=z)))).continuousWithinAt

/-- Uniform convergence on each positive-height half-plane gives actual continuity. -/
theorem principalWeightedSeries_continuousOn_halfplane {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) (a : ℝ) (ha : 0<a) :
    ContinuousOn (principalWeightedSeries b r j k σ) {z : ℝ × ℝ | a≤z.2} := by
  apply continuousOn_tsum
  · intro n
    exact (principalWeightedTerm_continuousOn b r j k σ n).mono (fun z hz => ha.trans_le hz)
  · exact (principalMomentMajorant_summable hb j k (2*Real.pi) a (by positivity) ha).mul_left 2
  · intro n z hz
    exact principalWeightedTerm_bound b r j k σ n a ha z hz

theorem principalWeightedSeries_continuousOn {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (j k σ : ℕ) : ContinuousOn (principalWeightedSeries b r j k σ) {z : ℝ × ℝ | 0<z.2} := by
  intro z hz
  change 0<z.2 at hz
  apply ContinuousAt.continuousWithinAt
  apply (principalWeightedSeries_continuousOn_halfplane hb r j k σ (z.2/2) (by linarith)).continuousAt
  exact continuous_snd.continuousAt.preimage_mem_nhds (Ici_mem_nhds (by linarith : z.2/2<z.2))

theorem principalWeightedSeries_zero (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) :
    principalWeightedSeries b r 0 0 σ = principalEulerCore b r σ := by
  funext z
  simp only [principalWeightedSeries,principalWeightedTerm,pow_zero,mul_one,
    principalEulerCore,principalEulerTerm]

#print axioms principalWeightedTerm_bound
#print axioms principalWeightedTerm_summable
#print axioms principalWeightedTerm_continuousOn
#print axioms principalWeightedSeries_continuousOn_halfplane
#print axioms principalWeightedSeries_continuousOn
#print axioms principalWeightedSeries_zero

end QuantitativeMaass
