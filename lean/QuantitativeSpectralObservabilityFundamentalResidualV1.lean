module

public import QuantitativeSpectralObservabilityFundamentalRowsV1
public import QuantitativeSpectralExceptionalFundamentalWitnessV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularBranchFamily
open QuantitativeSpectralExceptionalReducedRows
open QuantitativeSpectralFiniteReduction
open scoped MatrixGroups BigOperators lp

attribute [local instance] Classical.propDecidable

/-- The actual retained quotient residual factors through the original
rational row and a fixed finite signed-generator residual stack. All
piecewise reductions are constructed, and the identity holds for arbitrary
inputs at every root of the proved invariant conull set. -/
theorem exists_actual_quotient_residual_factorization {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (b : I → Branch) (c : I → ℂ) :
    ∃ C B : ℝ, ∃ n : ℕ, ∃ w : Fin n → I → List SL(2,ℤ),
      ∃ hw : ∀ j i a, a∈w j i → a∈signedGenerators S,
      ∃ E : ℝ → Fin n → Set ℍ,
      0<C ∧ 0<B ∧ (∀ H j, MeasurableSet (E H j)) ∧
      (∀ H, Pairwise (fun j k => Disjoint (E H j) (E H k))) ∧
      ∀ H : ℝ, B≤H → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t)
        (x : ℍ), fundamentalGood N x → ∀ (v : ℓ²(OrbitGroup,ℂ)) (g : OrbitGroup),
        let hs := wideCompactCover_compact N hN (H/C)
        let Ds := QuantitativeSpectralExceptionalUnweight.data hs hε t
        let Db := fun i => QuantitativeSpectralExceptionalUnweight.data (image_compact (b i) hs) hε t
        selectedGeneratorRecombine (signedGenerators S) b w hw c (E H) hs hε t Ds Db x
            (commonResidualStack (signedGenerators S) b w c hs hε t x v) g =
          if g • x∈openCover N \ wideTailCover N (H/C) then
            ∑ i, c i*coordinate N ε t x (label (b i)*g)
              (fundamentalSampling N hN H hε ht x v) else 0 := by
  obtain ⟨C,B,n,w,hw,E,hC,hB,hΓ,hE,hd,hall⟩ :=
    exists_fundamental_generator_factorization_with_geometry N hN S hS b c
  refine ⟨C,B,n,w,hw,E,hC,hB,hE,hd,?_⟩
  intro H hH ε hε t ht x hx v g
  obtain ⟨hcover,_,hred,hfac⟩ := hall H hH
  have he := selectedFundamentalFamily_coordinate_row N hN H b w hΓ c (E H)
    (hd H) hred hε ht x hx v g
  rw [hcover,hfac ε hε t x] at he
  by_cases hg : g • x∈openCover N \ wideTailCover N (H/C)
  · simpa only [ContinuousLinearMap.comp_apply,ite_eq_left hg] using he
  · simpa only [ContinuousLinearMap.comp_apply,ite_eq_right hg] using he

#print axioms exists_actual_quotient_residual_factorization

end QuantitativeSpectralObservability
