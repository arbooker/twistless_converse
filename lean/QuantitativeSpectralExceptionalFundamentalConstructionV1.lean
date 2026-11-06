module

public import QuantitativeSpectralExceptionalFundamentalAssemblyV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane Set MeasureTheory AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalGeometry
open scoped MatrixGroups

def signedGenerators (S : Finset SL(2,ℤ)) : Finset SL(2,ℤ) := S ∪ S.image Inv.inv

theorem mem_signedGenerators (S : Finset SL(2,ℤ)) (a : SL(2,ℤ))
    (ha : a ∈ S ∨ a⁻¹ ∈ S) : a ∈ signedGenerators S := by
  classical
  rcases ha with ha | ha
  · exact Finset.mem_union_left _ ha
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a⁻¹,ha,inv_inv a⟩)

/-- Fully constructed retained FD row factorization. The finite measurable
pieces and fixed words are proved to exist by rational cusp geometry; the
single residual stack uses only the original compact rational row and the
fixed signed generators on their explicit common compact region. No
geometric reduction, cap-bound, or operator reconstruction premise remains. -/
theorem exists_fundamental_generator_factorization {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) (c : ι → ℂ) :
    ∃ C B : ℝ, ∃ n : ℕ, ∃ w : Fin n → ι → List SL(2,ℤ),
      ∃ hw : ∀ j i a, a ∈ w j i → a ∈ signedGenerators S,
      ∃ E : ℝ → Fin n → Set ℍ,
      0 < C ∧ 0 < B ∧
      (∀ H j, MeasurableSet (E H j)) ∧
      (∀ H, Pairwise (fun j k => Disjoint (E H j) (E H k))) ∧
      ∀ H : ℝ, B ≤ H →
        (⋃ j, E H j) = openCover N \ wideTailCover N (H/C) ∧
        (∀ j, E H j ⊆ wideCompactCover N (H/C)) ∧
        ∀ (ε : ℝ) (hε : 0 < ε) (t : ℕ) (x : ℍ),
          let hs := wideCompactCover_compact N hN (H/C)
          let Ds := QuantitativeSpectralExceptionalUnweight.data hs hε t
          let Db := fun i => QuantitativeSpectralExceptionalUnweight.data (image_compact (b i) hs) hε t
          selectedFundamentalFamily N hN H b w c (E H) hε t x =
            (selectedGeneratorRecombine (signedGenerators S) b w hw c (E H) hs hε t Ds Db x).comp
              (commonResidualStack (signedGenerators S) b w c hs hε t x) := by
  obtain ⟨C,B,n,w,E,hC,hB,hW,hE,hdisj,hgeo⟩ := finite_fundamental_partition N hN S hS b
  have hw : ∀ j i a, a ∈ w j i → a ∈ signedGenerators S :=
    fun j i a ha => mem_signedGenerators S a (hW j i a ha)
  refine ⟨C,B,n,w,hw,E,hC,hB,hE,hdisj,?_⟩
  intro H hH
  obtain ⟨hcover,hsub,hred⟩ := hgeo H hH
  refine ⟨hcover,hsub,?_⟩
  intro ε hε t x
  exact selected_generator_factorization N hN H (signedGenerators S) b w hw c (E H)
    (wideCompactCover_compact N hN (H/C)) hsub (fun j i z hz => hred j z hz i) hε t _ _ x

#print axioms exists_fundamental_generator_factorization

end QuantitativeSpectralExceptionalReducedRows
