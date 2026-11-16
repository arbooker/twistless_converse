module

public import QuantitativeArithmeticMaassWavePDEV1
public import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

open QuantitativeArithmeticMaassWave

private theorem inner_quarter_sub {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (u v f : H) :
    inner ℂ ((1/4 : ℂ) • u-v) f=(1/4 : ℂ)*inner ℂ u f-inner ℂ v f := by
  simp only [inner_sub_left,inner_smul_left,map_div₀,map_one,map_ofNat]

theorem shiftedWave_inner (N : ℕ) (t : ℝ) (u f : AutomorphicSpace N) :
    inner ℂ (shiftedQuotientWave N t u) f=inner ℂ u (shiftedQuotientWave N t f) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (shiftedQuotientWave_isSelfAdjoint N t) u f

/-- Testing the wave against operator-domain vectors differentiates even when
the initial state is only L2. Symmetry transfers derivatives to the test. -/
theorem weakWave_hasDerivAt (N : ℕ) (f : AutomorphicSpace N)
    {u v : AutomorphicSpace N} (huv : FriedrichsGraph N u v) (t : ℝ) :
    HasDerivAt (fun s => inner ℂ u (shiftedQuotientWave N s f))
      (inner ℂ (quotientWaveVelocity N u v t) f) t := by
  have he : (fun s => inner ℂ u (shiftedQuotientWave N s f))=
      (fun s => inner ℂ (shiftedQuotientWave N s u) f) :=
    funext (fun s => (shiftedWave_inner N s u f).symm)
  rw [he]
  simpa only [inner_zero_right,zero_add] using
    (quotientWave_hasDerivAt N huv t).inner ℂ (hasDerivAt_const t f)

/-- The actual weak shifted wave equation on the full quotient Hilbert space.
No strong derivative or smooth representative of the evolving state is assumed. -/
theorem weakWave_second_derivative (N : ℕ) (f : AutomorphicSpace N)
    {u v : AutomorphicSpace N} (huv : FriedrichsGraph N u v) (t : ℝ) :
    HasDerivAt (deriv (fun s => inner ℂ u (shiftedQuotientWave N s f)))
      ((1/4 : ℂ)*inner ℂ u (shiftedQuotientWave N t f)-
        inner ℂ v (shiftedQuotientWave N t f)) t := by
  have he : deriv (fun s => inner ℂ u (shiftedQuotientWave N s f))=
      fun s => inner ℂ (quotientWaveVelocity N u v s) f :=
    funext (fun s => (weakWave_hasDerivAt N f huv s).deriv)
  rw [he]
  have h := (quotientWaveVelocity_hasDerivAt N u v t).inner ℂ (hasDerivAt_const t f)
  simp only [inner_zero_right,zero_add] at h
  apply h.congr_deriv
  exact (inner_quarter_sub (shiftedQuotientWave N t u) (shiftedQuotientWave N t v) f).trans
    (by rw [shiftedWave_inner,shiftedWave_inner])

/-- Compact smooth test seeds yield the literal distributional Laplacian in
the weak wave equation; the only evolving datum is an arbitrary L2 vector. -/
theorem poincare_weakWave_equation (N : ℕ) (f : AutomorphicSpace N)
    (u : SmoothUpperSeed) (t : ℝ) :
    deriv (deriv (fun s => inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N s f))) t=
      (1/4 : ℂ)*inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N t f)-
        inner ℂ (poincareSeedVector N u.laplacian) (shiftedQuotientWave N t f) :=
  (weakWave_second_derivative N f (friedrichsGraph_poincareSeed N u) t).deriv

theorem poincare_weakWave_initial (N : ℕ) (f : AutomorphicSpace N) (u : SmoothUpperSeed) :
    inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N 0 f)=
      inner ℂ (poincareSeedVector N u) f ∧
    deriv (fun s => inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N s f)) 0=0 := by
  constructor
  · rw [shiftedQuotientWave_zero,ContinuousLinearMap.id_apply]
  · rw [(weakWave_hasDerivAt N f (friedrichsGraph_poincareSeed N u) 0).deriv,
      quotientWaveVelocity_zero,inner_zero_left]

#print axioms weakWave_second_derivative
#print axioms poincare_weakWave_equation
#print axioms poincare_weakWave_initial

end QuantitativeMaass.Wave
