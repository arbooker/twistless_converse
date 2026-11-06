module

public import QuantitativeSpectralObservabilityFundamentalResidualV1
public import QuantitativeSpectralExceptionalPolynomialGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction
open scoped MatrixGroups BigOperators lp

attribute [local instance] Classical.propDecidable

/-- One set of actual geometric witnesses simultaneously gives the
literal retained quotient residual identity and a uniform polynomial
operator bound. All constants, words and piece counts are fixed before
the cusp cutoff, cap scale, exponent and orbit root are chosen. -/
theorem exists_quantitative_actual_quotient_residual {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (b : I → Branch) (c : I → ℂ) :
    ∃ C B L K : ℝ, ∃ n : ℕ, ∃ w : Fin n → I → List SL(2,ℤ),
      ∃ hw : ∀ j i a, a∈w j i → a∈signedGenerators S,
      ∃ E : ℝ → Fin n → Set ℍ,
      0<C ∧ 0<B ∧ 1≤L ∧ 1≤K ∧
      (∀ j i, (w j i).prod∈CongruenceSubgroup.Gamma0 N) ∧
      (∀ H j, MeasurableSet (E H j)) ∧
      (∀ H, Pairwise (fun j k => Disjoint (E H j) (E H k))) ∧
      ∀ H : ℝ, B≤H →
        (⋃ j, E H j)=openCover N \ wideTailCover N (H/C) ∧
        (∀ j, E H j⊆wideCompactCover N (H/C)) ∧
        (∀ j i z, z∈E H j →
          (AsymptoticCongruenceLabels.integralLabel (w j i).prod*label (b i)) • z∈fundamentalCompact N H) ∧
        ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (x : ℍ),
          let hs := wideCompactCover_compact N hN (H/C)
          let Ds := QuantitativeSpectralExceptionalUnweight.data hs hε t
          let Db := fun i => QuantitativeSpectralExceptionalUnweight.data (image_compact (b i) hs) hε t
          let A := selectedGeneratorRecombine (signedGenerators S) b w hw c (E H) hs hε t Ds Db x
          let D := commonResidualStack (signedGenerators S) b w c hs hε t x
          ‖A‖≤L*(1+ε*K*(H/C+3)^2)^(2*t) ∧
          selectedFundamentalFamily N hN H b w c (E H) hε t x=A.comp D ∧
          ∀ (ht : 1≤t), fundamentalGood N x →
            ∀ (v : ℓ²(OrbitGroup,ℂ)) (g : OrbitGroup),
              A (D v) g = if g • x∈openCover N \ wideTailCover N (H/C) then
                ∑ i, c i*coordinate N ε t x (label (b i)*g)
                  (fundamentalSampling N hN H hε ht x v) else 0 := by
  obtain ⟨C,B,n,w,hw,E,hC,hB,hΓ,hE,hd,hall⟩ :=
    exists_fundamental_generator_factorization_with_geometry N hN S hS b c
  obtain ⟨K,hK,hpoly⟩ := exists_selectedRecombine_polynomial_growth N hN b w
  let L : ℝ := max 1 (∑ j, (1+∑ i, ‖c i‖*((w j i).length:ℝ)))
  refine ⟨C,B,L,K,n,w,hw,E,hC,hB,le_max_left _ _,hK,hΓ,hE,hd,?_⟩
  intro H hH
  obtain ⟨hcover,hsub,hred,hfac⟩ := hall H hH
  refine ⟨hcover,hsub,hred,?_⟩
  intro ε hε t x
  refine ⟨?_,hfac ε hε t x,?_⟩
  · apply (hpoly (H/C) ε hε t (signedGenerators S) hw c (E H) _ _ x).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro ht hx v g
    have he := selectedFundamentalFamily_coordinate_row N hN H b w hΓ c (E H)
      (hd H) hred hε ht x hx v g
    rw [hcover,hfac ε hε t x] at he
    by_cases hg : g • x∈openCover N \ wideTailCover N (H/C)
    · simpa only [ContinuousLinearMap.comp_apply,ite_eq_left hg] using he
    · simpa only [ContinuousLinearMap.comp_apply,ite_eq_right hg] using he

#print axioms exists_quantitative_actual_quotient_residual

end QuantitativeSpectralExceptionalReducedRows
