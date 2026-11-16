module

public import QuantitativeMaassMixedTraceLinearV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The actual local Hilbert trace formed from the canonical moving-window columns. -/
def windowVolumeOperatorTrace (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) : ℝ :=
  ∫ x in S,(inner ℂ (A (windowAbelColumn N K he hc R hR a b x))
    (windowAbelColumn N K he hc R hR a b x)).re ∂volume

theorem windowVolumeOperatorTrace_integrable (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (hS : IsCompact S)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    IntegrableOn (fun x => (inner ℂ (A (windowAbelColumn N K he hc R hR a b x))
      (windowAbelColumn N K he hc R hR a b x)).re) S volume := by
  have hcol := windowAbelColumn_continuous N K he hc R hR a b
  exact (Complex.continuous_re.comp ((A.continuous.comp hcol).inner hcol)).continuousOn.integrableOn_compact hS

theorem windowVolumeOperatorTrace_add (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (hS : IsCompact S)
    (A B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    windowVolumeOperatorTrace N K he hc R hR a b S (A+B)=
      windowVolumeOperatorTrace N K he hc R hR a b S A+
      windowVolumeOperatorTrace N K he hc R hR a b S B := by
  unfold windowVolumeOperatorTrace
  simp only [add_apply,inner_add_left,Complex.add_re]
  exact integral_add (windowVolumeOperatorTrace_integrable N K he hc R hR a b S hS A)
    (windowVolumeOperatorTrace_integrable N K he hc R hR a b S hS B)

theorem windowVolumeOperatorTrace_smul (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R)
    (a b : ℝ) (S : Set ℍ) (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (c : ℝ) :
    windowVolumeOperatorTrace N K he hc R hR a b S (c • A)=
      c*windowVolumeOperatorTrace N K he hc R hR a b S A := by
  unfold windowVolumeOperatorTrace
  have hh (x : ℍ) : inner ℂ (c • A (windowAbelColumn N K he hc R hR a b x))
      (windowAbelColumn N K he hc R hR a b x)=
      c • inner ℂ (A (windowAbelColumn N K he hc R hR a b x))
      (windowAbelColumn N K he hc R hR a b x) :=
    inner_smul_left_eq_smul (𝕜 := ℂ)
      (A (windowAbelColumn N K he hc R hR a b x)) (windowAbelColumn N K he hc R hR a b x) c
  simp only [smul_apply,hh,Complex.smul_re]
  exact integral_const_mul _ _


#print axioms windowVolumeOperatorTrace_add
#print axioms windowVolumeOperatorTrace_smul
end QuantitativeMaass
