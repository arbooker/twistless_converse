module

public import AsymptoticNewSpaceCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace
open scoped ENNReal

/-- The normalization in the local root-to-trace comparison is strictly
positive at every positive level. -/
theorem projection_trace_toReal_pos (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) : 0<(trace volume (projection N hε ht)).toReal := by
  let : NeZero N := ⟨hN.ne'⟩
  have hi : 0<((gamma N).subgroupOf (gamma 1)).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_iff_finite.mpr inferInstance)
  rw [projection_trace_covolume_toReal N hN hε ht]
  exact mul_pos (by exact_mod_cast hi) (div_pos Real.pi_pos (by norm_num))

#print axioms projection_trace_toReal_pos

end AsymptoticCongruenceQuotient

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticRegularTrace
open scoped lp ENNReal

variable (N : ℕ) (J K : Subgroup AsymptoticRationalGroup.Group)
variable (hJ : gamma N≤J) (hK : gamma N≤K)
variable [Finite (J ⧸ (gamma N).subgroupOf J)] [Finite (K ⧸ (gamma N).subgroupOf K)]
variable {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

/-- The local trace formulas already proved in the strip model determine
the fixed coset new-projection coefficient. -/
theorem newSpace_trace_root :
    (trace volume (fun z => (newSpace N J K hJ hK hε ht z).starProjection)).toReal=
      (matrix (AsymptoticQuotientOperators.newSpace hJ hK).starProjection
        (classOf N 1) (classOf N 1)).re*
          (trace volume (projection N hε ht)).toReal := by
  have hn : 0≤(matrix (AsymptoticQuotientOperators.newSpace hJ hK).starProjection
      (classOf N 1) (classOf N 1)).re := by
    rw [AsymptoticQuotientOperators.projection_diagonal,Complex.ofReal_re]
    positivity
  simp_rw [newSpace_projection_compression N J K hJ hK hε ht]
  rw [compression_trace N hε ht _ hn,ENNReal.toReal_mul,ENNReal.toReal_ofReal hn]

theorem newSpace_root_of_trace (hN : 0<N) (c : ℝ)
    (hc : (trace volume (fun z => (newSpace N J K hJ hK hε ht z).starProjection)).toReal=
      (trace volume (projection N hε ht)).toReal*c) :
    (matrix (AsymptoticQuotientOperators.newSpace hJ hK).starProjection
      (classOf N 1) (classOf N 1)).re=c := by
  rw [newSpace_trace_root N J K hJ hK hε ht,mul_comm _ c] at hc
  exact mul_right_cancel₀ (projection_trace_toReal_pos N hN hε ht).ne' hc

#print axioms newSpace_trace_root
#print axioms newSpace_root_of_trace

end AsymptoticCongruenceOldSpace
