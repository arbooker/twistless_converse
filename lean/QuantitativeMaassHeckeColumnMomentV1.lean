module

public import QuantitativeMaassHeckeCuspProjectionV1
public import QuantitativeMaassHeckeWordKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace SchwartzMap FourierTransform ENNReal

namespace QuantitativeMaass

/-- The squared norm of the actual Hecke-power column is exactly its
even-degree finite correspondence kernel. -/
theorem hecke_column_norm_square_kernel (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (d : ℕ) (z : ℍ) :
    ‖((HeckeL2.operator N p hN hpN A B hAB)^d) (windowAbelColumn N K he hc R hR a b z)‖^2=
      (upperWindowKernel N p K hc R hR a b (2*d) HeckeUpper.root z).re := by
  let T := HeckeL2.operator N p hN hpN A B hAB
  let c := windowAbelColumn N K he hc R hR a b z
  have hT : (T^d).toLinearMap.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((HeckeL2.operator_selfAdjoint N p hN hpN A B hAB).pow d)
  have hh := hT ((T^d) c) c
  have hpow : (T^(2*d)) c=(T^d) ((T^d) c) := by
    rw [two_mul,pow_add]
    rfl
  change inner ℂ ((T^d) ((T^d) c)) c=inner ℂ ((T^d) c) ((T^d) c) at hh
  rw [←hpow] at hh
  calc
    _=(inner ℂ ((T^d) c) ((T^d) c)).re := (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _=(inner ℂ ((T^(2*d)) c) c).re := congrArg Complex.re hh.symm
    _=_ := congrArg Complex.re (windowAbelColumn_hecke_power N p hN hpN hNp A B hAB
      K he hc R hR a b (2*d) z)

/-- Actual cuspidal compact column moments are bounded by the literal
finite even-Hecke kernel, whose geometric branches are already identified. -/
theorem hecke_cuspidal_column_compact_moment (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (d : ℕ) (S : Set ℍ) :
    (∫⁻ z in S,ENNReal.ofReal (‖((HeckeL2.operator N p hN hpN A B hAB)^d)
      (localCuspidalProjection N hN (windowAbelColumn N K he hc R hR a b z))‖^2))≤
      ∫⁻ z in S,ENNReal.ofReal (upperWindowKernel N p K hc R hR a b (2*d) HeckeUpper.root z).re := by
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  rw [←hecke_column_norm_square_kernel N p hN hpN hNp A B hAB K he hc R hR a b d z]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hecke_power_cusp_projection_norm_le N p hN hpN A B hAB d _) 2

#print axioms hecke_column_norm_square_kernel
#print axioms hecke_cuspidal_column_compact_moment

end QuantitativeMaass
