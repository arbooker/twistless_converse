module

public import QuantitativeMaassCuspColumnMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

variable (N : ℕ) [NeZero N] (hN : 0<N) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ)

/-- Actual finite Bessel bound with the cusp constant mode removed. -/
theorem windowAbelColumn_centered_bessel {ι : Type*}
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i,v i∈localCuspidalSpace N hN) (s : SL(2,ℤ)) (u : ℝ)
    (z : ℍ) (S : Finset ι) :
    (∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2)≤
      ‖windowAbelColumn N K he hc R hR a b z-
        cuspColumnMean N (windowAbelColumn N K he hc R hR a b) s u‖^2 :=
  centered_column_bessel v hv _ _
    (fun i => windowAbelColumn_mean_orthogonal N hN K he hc R hR a b s u (v i) (hcus i)) S

/-- The raw compact window trace can be bounded by centered columns at any
chosen cusp height field. The removed term is proved orthogonal internally. -/
theorem windowWavePacket_raw_centered_bessel {ι : Type*}
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i,v i∈localCuspidalSpace N hN) (s : SL(2,ℤ)) (u : ℍ → ℝ)
    (S : Set ℍ) (hS : IsCompact S) :
    (∑' i,ENNReal.ofReal (‖quotientRestriction N S hS hS.measurableSet
      (windowWavePacket N K hc R hR a b (v i))‖^2))≤
      ∫⁻ z in S,ENNReal.ofReal (‖windowAbelColumn N K he hc R hR a b z-
        cuspColumnMean N (windowAbelColumn N K he hc R hR a b) s (u z)‖^2) := by
  apply continuous_column_raw_centered_bessel N _ _
    (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowAbelColumn_packet_coeFn N K he hc R hR a b) v hv S hS
  intro z _ i
  exact windowAbelColumn_mean_orthogonal N hN K he hc R hR a b s (u z) (v i) (hcus i)

#print axioms windowAbelColumn_centered_bessel
#print axioms windowWavePacket_raw_centered_bessel

end QuantitativeMaass
