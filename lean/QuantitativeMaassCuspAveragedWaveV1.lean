module

public import QuantitativeMaassCuspAveragedTestV1
public import QuantitativeMaassWaveWeakEquationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

/-- The literal bounded local height average tested against a continuous
vertical function along the actual quotient wave. -/
def cuspWaveTest (N : ℕ) (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a)
    (g : ℝ → ℂ) (hg : Continuous g) (f : AutomorphicSpace N) (t : ℝ) : ℂ :=
  inner ℂ (heightTestVector _ (upperRectangle_compact 0 N a b ha) g hg)
    (cuspConstantLocal N s a b ha (shiftedQuotientWave N t f))

/-- First weak time differentiability for arbitrary L2 initial states. -/
theorem cuspWaveTest_differentiable (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (ha : 0<a)
    (hs : Function.support g⊆Icc a b) (f : AutomorphicSpace N) :
    Differentiable ℝ (cuspWaveTest N s a b ha g hg.continuous f) := by
  let u := (cuspPeriodTest N (Nat.cast_pos.mpr hN) g hg a b ha hs).cuspPush s
  have he : (fun t => inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N t f))=
      cuspWaveTest N s a b ha g hg.continuous f :=
    funext (fun t => cuspPeriodTest_pairing N hN s g hg a b ha hs (shiftedQuotientWave N t f))
  intro t
  have h := (weakWave_hasDerivAt N f (friedrichsGraph_poincareSeed N u) t).differentiableAt
  rw [he] at h
  exact h

/-- The actual all-cusp averaged weak wave equation. The horizontal
second derivative has been eliminated by a proved compact partition and
Hilbert density, with no regularity assumption on the evolving state. -/
theorem cuspWaveTest_second_derivative (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (ha : 0<a)
    (hs : Function.support g⊆Icc a b) (f : AutomorphicSpace N) (t : ℝ) :
    HasDerivAt (deriv (cuspWaveTest N s a b ha g hg.continuous f))
      ((1/4:ℂ)*cuspWaveTest N s a b ha g hg.continuous f t-
        cuspWaveTest N s a b ha (heightLaplacianTest g) (heightLaplacianTest_continuous g hg) f t) t := by
  let u := cuspPeriodTest N (Nat.cast_pos.mpr hN) g hg a b ha hs
  have h := weakWave_second_derivative N f (friedrichsGraph_poincareSeed N (u.cuspPush s)) t
  have he : (fun t => inner ℂ (poincareSeedVector N (u.cuspPush s)) (shiftedQuotientWave N t f))=
      cuspWaveTest N s a b ha g hg.continuous f :=
    funext (fun t => cuspPeriodTest_pairing N hN s g hg a b ha hs (shiftedQuotientWave N t f))
  rw [he,poincare_cuspPush_laplacian] at h
  apply h.congr_deriv
  exact congrArg₂ (fun z v : ℂ => (1/4:ℂ)*z-v)
    (cuspPeriodTest_pairing N hN s g hg a b ha hs (shiftedQuotientWave N t f))
    (cuspPeriodTest_laplacian_pairing N hN s g hg a b ha hs (shiftedQuotientWave N t f))

/-- Exact zero initial velocity of the averaged weak solution. -/
theorem cuspWaveTest_initial_velocity (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (ha : 0<a)
    (hs : Function.support g⊆Icc a b) (f : AutomorphicSpace N) :
    deriv (cuspWaveTest N s a b ha g hg.continuous f) 0=0 := by
  let u := (cuspPeriodTest N (Nat.cast_pos.mpr hN) g hg a b ha hs).cuspPush s
  have he : (fun t => inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N t f))=
      cuspWaveTest N s a b ha g hg.continuous f :=
    funext (fun t => cuspPeriodTest_pairing N hN s g hg a b ha hs (shiftedQuotientWave N t f))
  rw [← he]
  exact (poincare_weakWave_initial N f u).2

#print axioms cuspWaveTest_differentiable
#print axioms cuspWaveTest_second_derivative
#print axioms cuspWaveTest_initial_velocity

end QuantitativeMaass.Wave
