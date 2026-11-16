module

public import QuantitativeMaassRawColumnBesselV1
public import QuantitativeMaassTranslatedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

variable (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ)

/-- The canonical actual window columns are invariant under the level group. -/
theorem windowAbelColumn_invariant (γ : gamma N) (z : ℍ) :
    windowAbelColumn N K he hc R hR a b (γ•z)=windowAbelColumn N K he hc R hR a b z := by
  unfold windowAbelColumn timeAbelColumn
  apply oneSidedAbelColumn_invariant

/-- The canonical column evaluates the actual original-window operator. -/
theorem windowAbelColumn_packet_coeFn (v : AutomorphicSpace N) :
    (windowWavePacket N K hc R hR a b v).val=ᵐ[quotientMeasure N]
      (fun x => inner ℂ (windowAbelColumn N K he hc R hR a b x) v) := by
  unfold windowAbelColumn
  exact timeAbelColumn_packet_coeFn N (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR) (symmetricWindowTimeTest_even K he R a b)
    (symmetricWindowTimeTest_real K he R a b)
    ((symmetricWindowTimeTest_uniform_support K hc).choose*R)
    (mul_nonneg (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1.le hR.le)
    ((symmetricWindowTimeTest_uniform_support K hc).choose_spec.2 R hR a b) v

/-- A global diagonal identity, including the literal spherical identity and
all actual nonidentity terms. This holds before any measure restriction. -/
theorem windowAbelColumn_norm_square (x : ℍ) :
    ‖windowAbelColumn N K he hc R hR a b x‖^2=
      (windowIdentityContribution K hc R hR a b).re+
        (windowGeometricRemainder N K hc R hR a b x).re := by
  have hh : inner ℂ (windowAbelColumn N K he hc R hR a b x)
      (windowAbelColumn N K he hc R hR a b x)=
      windowIdentityContribution K hc R hR a b+windowGeometricRemainder N K hc R hR a b x := by
    unfold windowAbelColumn
    rw [timeSquare_kernel_cross N _ _ _ (symmetricWindowTimeTest_real K he R a b)]
    exact windowTimeSquare_kernel_split N K hc R hR a b x
  have hh' := congrArg Complex.re hh
  have hself : (inner ℂ (windowAbelColumn N K he hc R hR a b x)
      (windowAbelColumn N K he hc R hR a b x)).re=‖windowAbelColumn N K he hc R hR a b x‖^2 :=
    inner_self_eq_norm_sq (𝕜:=ℂ) _
  rw [hself] at hh'
  exact hh'

/-- Bessel's inequality on the actual raw compact restriction, for the
original-window packet and arbitrary orthonormal families. -/
theorem windowWavePacket_raw_compact_bessel {ι : Type*}
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v) (S : Set ℍ) (hS : IsCompact S) :
    (∑' i,ENNReal.ofReal (‖quotientRestriction N S hS hS.measurableSet
      (windowWavePacket N K hc R hR a b (v i))‖^2))≤
      ∫⁻ x in S,ENNReal.ofReal (‖windowAbelColumn N K he hc R hR a b x‖^2) :=
  continuous_column_raw_bessel N _ _ (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowAbelColumn_packet_coeFn N K he hc R hR a b) v hv S hS

#print axioms windowAbelColumn_invariant
#print axioms windowAbelColumn_packet_coeFn
#print axioms windowAbelColumn_norm_square
#print axioms windowWavePacket_raw_compact_bessel

end QuantitativeMaass
