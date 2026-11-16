module

public import QuantitativeMaassBroadCompactFactorV1
public import QuantitativeMaassCountableBasisV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal

namespace QuantitativeMaass

/-- The actual compact-input broad transfer has its source-column energy
bounded by the compact deficit-column trace. Global square integrability
of the source columns is not required. -/
theorem broadCompact_source_column_energy_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ, A v =ᵐ[μ] (fun z => inner ℂ (c z) v))
    (N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L) (t : ℝ)
    (K : Set ℍ) (hK : IsCompact K)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : IsSelfAdjoint D)
    (C : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 μ) :
    (∫⁻ z, ENNReal.ofReal (‖D (broadQuotientPacket N L hL t
      ((quotientRestriction N K hK hK.measurableSet).adjoint (C.adjoint (c z))))‖^2) ∂μ) ≤
      ENNReal.ofReal (‖A‖^2)*ENNReal.ofReal (‖C‖^2)*
        ∫⁻ w in K, ENNReal.ofReal (‖D (broadAbelColumn N L hL t w)‖^2) := by
  obtain ⟨ι,hι,⟨basis⟩⟩ := exists_countable_automorphic_basis N
  let : Countable ι := hι
  have hh := kernel_compact_factor_column_energy_le μ (volume.restrict K) basis A c hc
    (fun w => D (broadAbelColumn N L hL t w))
    (compact_column_memLp _ (D.continuous.comp (broadAbelColumn_continuous N L hL t)) K hK) C
  rw [broadCompact_column_operator_adjoint N L hL t K hK D hD] at hh
  simpa only [comp_apply] using hh

#print axioms broadCompact_source_column_energy_le

end QuantitativeMaass
