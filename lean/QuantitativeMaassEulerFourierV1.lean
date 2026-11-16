module

public import QuantitativeMaassEulerPhaseV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- The actual principal Fourier--Bessel summand, without the common sqrt(y). -/
def principalEulerTerm (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (z : ℝ × ℝ) : ℂ :=
  b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*z.2):ℂ)*
    eulerParityPhase σ (n+1) z.1

def principalEulerCore (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (z : ℝ × ℝ) : ℂ :=
  ∑' n,principalEulerTerm b r σ n z

/-- The original unweighted principal Maass Fourier--Bessel reconstruction. -/
def principalEulerWave (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (z : ℝ × ℝ) : ℂ :=
  (Real.sqrt z.2:ℂ)*principalEulerCore b r σ z

theorem principalEulerTerm_bound (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (a : ℝ) (ha : 0<a)
    (z : ℝ × ℝ) (hz : a≤z.2) :
    ‖principalEulerTerm b r σ n z‖≤2*principalMomentMajorant b 0 0 (2*Real.pi) a n := by
  unfold principalEulerTerm
  rw [norm_mul,norm_mul,Complex.norm_real]
  calc
    _ ≤ ‖b (n+1)‖*‖MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*z.2)‖*2 := by
      gcongr
      exact eulerParityPhase_norm_le σ (n+1) z.1
    _ ≤ _ := by
      have hh := principalMomentMajorant_bound b 0 0 r (2*Real.pi) a (by positivity) ha n z.2 hz
      simpa only [pow_zero,mul_one,mul_comm (2:ℝ)] using mul_le_mul_of_nonneg_right hh (by norm_num : (0:ℝ)≤2)

theorem principalEulerTerm_summable {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (z : ℝ × ℝ) (hz : 0<z.2) :
    Summable (fun n => principalEulerTerm b r σ n z) := by
  apply Summable.of_norm_bounded
    ((principalMomentMajorant_summable hb 0 0 (2*Real.pi) z.2 (by positivity) hz).mul_left 2)
  intro n
  exact principalEulerTerm_bound b r σ n z.2 hz z le_rfl

theorem principalEulerTerm_continuousOn (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) :
    ContinuousOn (principalEulerTerm b r σ n) {z : ℝ × ℝ | 0<z.2} := by
  intro z hz
  change 0<z.2 at hz
  have hp : 0<2*Real.pi*((n+1:ℕ):ℝ)*z.2 := by positivity
  have hc := (MaassKBessel.moment_hasDerivAt 0 r hp).continuousAt.comp (f:=fun w : ℝ × ℝ => 2*Real.pi*((n+1:ℕ):ℝ)*w.2)
    (by fun_prop : ContinuousAt (fun w : ℝ × ℝ => 2*Real.pi*((n+1:ℕ):ℝ)*w.2) z)
  have hm := Complex.continuous_ofReal.continuousAt.comp (f:=fun w : ℝ × ℝ => MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*w.2)) hc
  exact ((continuousAt_const.mul hm).mul
    ((eulerParityPhase_continuous σ (n+1)).continuousAt.comp (f:=Prod.fst) (continuous_fst.continuousAt (x:=z)))).continuousWithinAt

/-- Uniform convergence on each positive-height half-plane gives actual continuity. -/
theorem principalEulerCore_continuousOn_halfplane {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (a : ℝ) (ha : 0<a) :
    ContinuousOn (principalEulerCore b r σ) {z : ℝ × ℝ | a≤z.2} := by
  apply continuousOn_tsum
  · intro n
    exact (principalEulerTerm_continuousOn b r σ n).mono (fun z hz => ha.trans_le hz)
  · exact (principalMomentMajorant_summable hb 0 0 (2*Real.pi) a (by positivity) ha).mul_left 2
  · intro n z hz
    exact principalEulerTerm_bound b r σ n a ha z hz

theorem principalEulerCore_continuousOn {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) : ContinuousOn (principalEulerCore b r σ) {z : ℝ × ℝ | 0<z.2} := by
  intro z hz
  change 0<z.2 at hz
  apply ContinuousAt.continuousWithinAt
  apply (principalEulerCore_continuousOn_halfplane hb r σ (z.2/2) (by linarith)).continuousAt
  exact continuous_snd.continuousAt.preimage_mem_nhds (Ici_mem_nhds (by linarith : z.2/2<z.2))

theorem principalEulerWave_continuousOn {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) : ContinuousOn (principalEulerWave b r σ) {z : ℝ × ℝ | 0<z.2} :=
  (by fun_prop : Continuous (fun z : ℝ × ℝ => (Real.sqrt z.2:ℂ))).continuousOn.mul
    (principalEulerCore_continuousOn hb r σ)

theorem principalEulerWave_periodic (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (y : ℝ) :
    Function.Periodic (fun x => principalEulerWave b r σ (x,y)) 1 := by
  intro x
  unfold principalEulerWave principalEulerCore
  apply congrArg (fun w : ℂ => (Real.sqrt y:ℂ)*w)
  apply tsum_congr
  intro n
  unfold principalEulerTerm
  rw [eulerParityPhase_periodic σ (n+1) x]

theorem principalEulerWave_reflection (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (x y : ℝ) :
    principalEulerWave b r σ (-x,y)=(-1:ℂ)^σ*principalEulerWave b r σ (x,y) := by
  have he : principalEulerCore b r σ (-x,y)=(-1:ℂ)^σ*principalEulerCore b r σ (x,y) := by
    unfold principalEulerCore
    rw [←tsum_mul_left]
    apply tsum_congr
    intro n
    unfold principalEulerTerm
    rw [eulerParityPhase_reflection]
    ring
  unfold principalEulerWave
  rw [he]
  ring

#print axioms principalEulerTerm_bound
#print axioms principalEulerTerm_summable
#print axioms principalEulerTerm_continuousOn
#print axioms principalEulerCore_continuousOn_halfplane
#print axioms principalEulerCore_continuousOn
#print axioms principalEulerWave_continuousOn
#print axioms principalEulerWave_periodic
#print axioms principalEulerWave_reflection

end QuantitativeMaass
