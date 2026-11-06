module

public import QuantitativeEulerEndpointNormalizedCombinedPacketV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open ContinuousLinearMap AsymptoticObservationStack AsymptoticPolarIsometry
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch QuantitativeHolomorphic

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The detector's square root cancels exactly from its composed Gram. -/
theorem absolute_stack_composed_gram (L : ι → H →L[ℂ] H) (U : H →L[ℂ] H) :
    star (absolute (stack L)*U)*(absolute (stack L)*U)=∑ i,star (L i*U)*(L i*U) := by
  have ha : star (absolute (stack L))*absolute (stack L)=∑ i,star (L i)*L i :=
    (absolute_gram (stack L)).trans (stack_gram L)
  calc
    _ = star U*(star (absolute (stack L))*absolute (stack L))*U := by simp only [star_mul,mul_assoc]
    _ = star U*(∑ i,star (L i)*L i)*U := congrArg (fun T => star U*T*U) ha
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_mul,star_mul,mul_assoc]
end Hilbert

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- The combined packet energy is a finite sum of the original baseline and
prime-row Grams; no square-root detector remains in this polynomial input. -/
theorem normalized_combined_gram_expansion (x : UpperHalfPlane) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let U := normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x
    (∑ i : Fin (l.length+1),star (normalizedCombinedRows A P e hs l i x)*normalizedCombinedRows A P e hs l i x)=
      (∑ i : NewBaselineIndex N,star (newBaselineRows N e hs P'.epsilon_pos (P'.s+4) x i*U)*
        (newBaselineRows N e hs P'.epsilon_pos (P'.s+4) x i*U))+
      ∑ i : Fin l.length,star (packetSequence N (NeZero.pos N) (sign e.1) hs P'.epsilon_pos (P'.s+4) l i x*U)*
        (packetSequence N (NeZero.pos N) (sign e.1) hs P'.epsilon_pos (P'.s+4) l i x*U) := by
  intro P' U
  rw [Fin.sum_univ_succ]
  change star (newBaselineDetector N e hs P'.epsilon_pos (P'.s+4) x*U)*
      (newBaselineDetector N e hs P'.epsilon_pos (P'.s+4) x*U)+_= _
  rw [newBaselineDetector,absolute_stack_composed_gram]
  rfl

#print axioms absolute_stack_composed_gram
#print axioms normalized_combined_gram_expansion
end QuantitativeEulerEndpointPrepared
