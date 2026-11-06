module

public import QuantitativeEulerEndpointReplacementGramBoundsV1
public import QuantitativeEulerEndpointTerminalUnitExpressionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBlockNormalization
open scoped Classical
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)
    (e : Sector N) {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

theorem replacementGram_support (C : ℕ → ℝ) (x : UpperHalfPlane)
    (U T : RegularSpace →L[ℂ] RegularSpace) (hT : IsStarProjection T) (hU : U*T=U) :
    T*replacementGram A P e hs l C x U=replacementGram A P e hs l C x U ∧
      replacementGram A P e hs l C x U*T=replacementGram A P e hs l C x U := by
  have hh := scaled_gram_sum_support T hT
    (fun i : Fin (l.length+1) => uncomposedCombinedRows A P e hs l i x)
    ((factor C (l.length+1):ℝ):ℂ) U hU
  have he : replacementGram A P e hs l C x U=
      ∑ i : Fin (l.length+1),
        star (((factor C (l.length+1):ℝ):ℂ) • (uncomposedCombinedRows A P e hs l i x*U))*
          (((factor C (l.length+1):ℝ):ℂ) • (uncomposedCombinedRows A P e hs l i x*U)) := by
    unfold replacementGram finiteRowGram
    apply Finset.sum_congr rfl
    intro i _
    change star ((((factor C (l.length+1):ℝ):ℂ) • uncomposedCombinedRows A P e hs l i x)*U)*
      ((((factor C (l.length+1):ℝ):ℂ) • uncomposedCombinedRows A P e hs l i x)*U)=_
    rw [smul_mul_assoc]
  rw [he]
  exact hh

#print axioms replacementGram_support
end QuantitativeEulerEndpointPrepared
