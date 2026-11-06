module

public import QuantitativeEulerEndpointBoundedGramReplacementV1
public import QuantitativeEulerEndpointNormalizedGramExpansionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch ContinuousLinearMap
open QuantitativeEulerEndpointBlockNormalization

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- The baseline square root cancels for any replacement reconstruction,
with the exact original block normalization retained on every row. -/
theorem replacementGram_expansion (C : ℕ → ℝ) (x : UpperHalfPlane) (U : Space →L[ℂ] Space) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let r : ℂ := (factor C (l.length+1):ℝ)
    replacementGram A P e hs l C x U=
      (∑ i : NewBaselineIndex N,star (r • (newBaselineRows N e hs P'.epsilon_pos (P'.s+4) x i*U))*
        (r • (newBaselineRows N e hs P'.epsilon_pos (P'.s+4) x i*U)))+
      ∑ i : Fin l.length,star (r • (packetSequence N (NeZero.pos N) (sign e.1) hs P'.epsilon_pos (P'.s+4) l i x*U))*
        (r • (packetSequence N (NeZero.pos N) (sign e.1) hs P'.epsilon_pos (P'.s+4) l i x*U)) := by
  intro P' r
  unfold replacementGram finiteRowGram
  rw [Fin.sum_univ_succ]
  simp only [smul_comp]
  change star (r • (newBaselineDetector N e hs P'.epsilon_pos (P'.s+4) x*U))*
    (r • (newBaselineDetector N e hs P'.epsilon_pos (P'.s+4) x*U))+_= _
  have hh := absolute_stack_composed_gram (newBaselineRows N e hs P'.epsilon_pos (P'.s+4) x) (r • U)
  apply congrArg₂ (fun X Y : Space →L[ℂ] Space => X+Y)
  · simpa only [newBaselineDetector,mul_smul_comm] using hh
  · rfl

#print axioms replacementGram_expansion
end QuantitativeEulerEndpointPrepared
