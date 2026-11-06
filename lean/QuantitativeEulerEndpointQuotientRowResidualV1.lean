module

public import QuantitativeSpectralObservabilityOldResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows QuantitativeSpectralObservability
open scoped MatrixGroups lp ENNReal Classical

/-- The genuine old-space projection of the actual quotient sampler is
a bounded recombination of the original old trace and fixed generator
defects, apart from an actual tail projection of trace O(1/H).
All constants and words are fixed before H, epsilon, t and x. -/
theorem exists_quotientRow_residual (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {I : Type*} [Fintype I] (b : I → Branch) (c : I → ℂ)
    (T : ∀ {ε : ℝ}, 0<ε → ∀ {t : ℕ}, 1≤t → ℍ → ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ))
    (hTrange : ∀ {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : ℓ²(OrbitGroup,ℂ)),
      T hε ht x v∈quotientSpace N hε ht x)
    (hTcoord : ∀ {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ)
      (v : ℓ²(OrbitGroup,ℂ)), v∈quotientSpace N hε ht x → ∀ g : OrbitGroup,
      coordinate N ε t x g (T hε ht x v)=∑ i,c i*coordinate N ε t x (label (b i)*g) v) :
    ∃ C B L K : ℝ, ∃ n : ℕ, ∃ w : Fin n → I → List SL(2,ℤ),
      ∃ _hw : ∀ j i a, a∈w j i → a∈signedGenerators S,
      0<C ∧ 0<B ∧ 1≤L ∧ 1≤K ∧
      ∀ H : ℝ, B≤H → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t)
        (x : ℍ),
        let hs := wideCompactCover_compact N hN (H/C)
        let D := commonResidualStack (signedGenerators S) b w c hs hε t x
        let P := T hε ht x
        ∃ R : GeneratorData (signedGenerators S) →L[ℂ] ℓ²(OrbitGroup,ℂ),
          ‖R‖≤L*(1+ε*K*(H/C+3)^2)^(2*t) ∧
          trace volume (fundamentalSubsetProjection N hε ht (fundamentalTail N (H/C)))≤
            (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H/C)⁻¹) ∧
          ∀ v : ℓ²(OrbitGroup,ℂ),
            P (fundamentalSampling N hN H hε ht x v)=R (D v)+
              fundamentalSubsetProjection N hε ht (fundamentalTail N (H/C)) x
                (P (fundamentalSampling N hN H hε ht x v)) := by
  obtain ⟨C,B,L,K,n,w,hw,E,hC,hB,hL,hK,_hΓ,_hE,_hd,hall⟩ :=
    exists_quantitative_actual_quotient_residual N hN S hS b c
  refine ⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,?_⟩
  intro H hH ε hε t ht x
  obtain ⟨_hcover,_hsub,_hred,hrow⟩ := hall H hH
  obtain ⟨hbound,_hfac,hcoord⟩ := hrow ε hε t x
  let hs := wideCompactCover_compact N hN (H/C)
  let A := selectedGeneratorRecombine (signedGenerators S) b w hw c (E H) hs hε t
    (QuantitativeSpectralExceptionalUnweight.data hs hε t)
    (fun i => QuantitativeSpectralExceptionalUnweight.data (image_compact (b i) hs) hε t) x
  refine ⟨retainedRecombiner N hε ht (H/C) x A,
    (retainedRecombiner_norm N hε ht (H/C) x A).trans hbound,
    fundamentalTailProjection_trace N hN hε ht (div_pos (lt_of_lt_of_le hB hH) hC),?_⟩
  intro v
  by_cases hx : fundamentalGood N x
  · apply quotient_row_decompose N hε ht (H/C) x hx
    · exact hTrange hε ht x _
    · intro g hg
      have hsamp := fundamentalSampling_range N hN H hε ht x v
      have ho := hTcoord hε ht x (fundamentalSampling N hN H hε ht x v) hsamp g
      have hc := hcoord ht hx v g
      simp only [ite_eq_left hg] at hc
      exact ho.trans hc.symm
  · simp only [fundamentalSampling,retainedRecombiner,fundamentalTransfer,
      dite_eq_right hx,zero_comp,zero_apply,map_zero,add_zero]

#print axioms exists_quotientRow_residual
end QuantitativeEulerEndpointPrepared
