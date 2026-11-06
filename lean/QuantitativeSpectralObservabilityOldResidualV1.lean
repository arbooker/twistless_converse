module

public import QuantitativeSpectralObservabilityRowTransferV1

set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups lp ENNReal

attribute [local instance] Classical.propDecidable

/-- A matrix representative of an actual positive projective label. -/
def projectiveBranch (g : OrbitGroup) : Branch :=
  ⟨Classical.choose g.val.property,
    AsymptoticRationalGroup.representative_positive g (Classical.choose_spec g.val.property)⟩

theorem projectiveBranch_label (g : OrbitGroup) : label (projectiveBranch g)=g := by
  apply Subtype.ext
  apply Subtype.ext
  exact Classical.choose_spec g.val.property

/-- The genuine old-space projection of the actual quotient sampler is
a bounded recombination of the original old trace and fixed generator
defects, apart from an actual tail projection of trace O(1/H).
All constants and words are fixed before H, epsilon, t and x. -/
theorem exists_oldProjection_residual (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (J : Subgroup OrbitGroup) (hJ : gamma N≤J)
    [Finite (J ⧸ (gamma N).subgroupOf J)]
    {I : Type*} [Fintype I] (r : I → J)
    (e : I ≃ (J ⧸ (gamma N).subgroupOf J))
    (he : ∀ i, e i=QuotientGroup.mk (r i)) :
    let b := fun i => projectiveBranch (r i).val⁻¹
    let c := fun _ : I => (((gamma N).subgroupOf J).index:ℂ)⁻¹
    ∃ C B L K : ℝ, ∃ n : ℕ, ∃ w : Fin n → I → List SL(2,ℤ),
      ∃ _hw : ∀ j i a, a∈w j i → a∈signedGenerators S,
      0<C ∧ 0<B ∧ 1≤L ∧ 1≤K ∧
      ∀ H : ℝ, B≤H → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t)
        (x : ℍ),
        let hs := wideCompactCover_compact N hN (H/C)
        let D := commonResidualStack (signedGenerators S) b w c hs hε t x
        let P := (AsymptoticCongruenceOldSpace.space N J hJ hε ht x).starProjection
        ∃ R : GeneratorData (signedGenerators S) →L[ℂ] ℓ²(OrbitGroup,ℂ),
          ‖R‖≤L*(1+ε*K*(H/C+3)^2)^(2*t) ∧
          trace volume (fundamentalSubsetProjection N hε ht (fundamentalTail N (H/C)))≤
            (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H/C)⁻¹) ∧
          ∀ v : ℓ²(OrbitGroup,ℂ),
            P (fundamentalSampling N hN H hε ht x v)=R (D v)+
              fundamentalSubsetProjection N hε ht (fundamentalTail N (H/C)) x
                (P (fundamentalSampling N hN H hε ht x v)) := by
  dsimp only
  let b := fun i => projectiveBranch (r i).val⁻¹
  let c := fun _ : I => (((gamma N).subgroupOf J).index:ℂ)⁻¹
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
    · exact oldProjection_range N J hJ hε ht x _
    · intro g hg
      have hsamp := fundamentalSampling_range N hN H hε ht x v
      have ho := oldProjection_coordinate N J hJ r e he hε ht x
        (fundamentalSampling N hN H hε ht x v) hsamp g
      have hc := hcoord ht hx v g
      simp only [ite_eq_left hg] at hc
      simp only [b,c,projectiveBranch_label] at hc
      exact ho.trans hc.symm
  · simp only [fundamentalSampling,retainedRecombiner,fundamentalTransfer,
      dite_eq_right hx,zero_comp,zero_apply,map_zero,add_zero]

#print axioms projectiveBranch_label
#print axioms exists_oldProjection_residual

end QuantitativeSpectralObservability
