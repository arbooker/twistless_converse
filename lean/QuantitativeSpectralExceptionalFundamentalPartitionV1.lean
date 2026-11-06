module

public import QuantitativeSpectralExceptionalFundamentalWordsV1
public import QuantitativeSpectralObservabilityFundamentalCompactV1
public import Mathlib.Order.Disjointed

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open UpperHalfPlane Set MeasureTheory AsymptoticRegularBranchFamily
open AsymptoticCongruenceLabels AsymptoticRationalBranches
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups

/-- The full retained quotient cover has a measurable finite partition into literal fundamental-domain sampling coordinates. This partition
with a fixed number of pieces and fixed actual generator-word reducers.
This supplies the geometric hypotheses of retained residual factorization
for every branch, uniformly over all later cusp cutoffs. -/
theorem finite_fundamental_partition {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) :
    ∃ C B : ℝ, ∃ n : ℕ, ∃ w : Fin n → ι → List SL(2,ℤ),
      ∃ E : ℝ → Fin n → Set ℍ,
      0 < C ∧ 0 < B ∧
      (∀ j i a, a ∈ w j i → a ∈ S ∨ a⁻¹ ∈ S) ∧
      (∀ H j, MeasurableSet (E H j)) ∧
      (∀ H, Pairwise (fun j k => Disjoint (E H j) (E H k))) ∧
      ∀ H : ℝ, B ≤ H →
        (⋃ j, E H j) = openCover N \ wideTailCover N (H/C) ∧
        (∀ j, E H j ⊆ wideCompactCover N (H/C)) ∧
        ∀ j z, z ∈ E H j → ∀ i,
          (integralLabel (w j i).prod * label (b i)) • z ∈ fundamentalCompact N H := by
  classical
  obtain ⟨C,B,hC,hB,W,hW,hr⟩ := finite_retained_fundamental_words N hN S hS b
  let J := ι → ↥W
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let w : Fin (Fintype.card J) → ι → List SL(2,ℤ) := fun j i => (e j i).val
  let R (H : ℝ) := openCover N \ wideTailCover N (H/C)
  let P (H : ℝ) (j : Fin (Fintype.card J)) : Set ℍ := R H ∩
    ⋂ i, (fun z => (integralLabel (w j i).prod * label (b i)) • z) ⁻¹' fundamentalCompact N H
  have hP (H j) : MeasurableSet (P H j) :=
    ((openCover_open N).measurableSet.diff (wideTailCover_measurable N hN (H/C))).inter
      (MeasurableSet.iInter (fun i => (fundamentalCompact_compact N hN H).measurableSet.preimage
        (action_continuous _).measurable))
  have hUnion (H : ℝ) (hH : B ≤ H) : (⋃ j, P H j) = R H := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact hj.1
    · intro z hz
      choose v hv hred using hr H hH z hz
      let f : J := fun i => ⟨v i,hv i⟩
      refine mem_iUnion.mpr ⟨e.symm f,hz,?_⟩
      have he : w (e.symm f) = v := by
        funext i
        simp only [w,Equiv.apply_symm_apply]
        rfl
      apply mem_iInter.mpr
      intro i
      simpa only [mem_preimage,he] using hred i
  refine ⟨C,B,Fintype.card J,w,fun H => disjointed (P H),hC,hB,?_,?_,?_,?_⟩
  · intro j i a ha
    exact hW _ (e j i).property a ha
  · intro H j
    change MeasurableSet (disjointed (P H) j)
    rw [disjointed_eq_inter_compl]
    exact (hP H j).inter (MeasurableSet.iInter (fun k =>
      MeasurableSet.iInter (fun _ => (hP H k).compl)))
  · intro H
    exact disjoint_disjointed (P H)
  · intro H hH
    refine ⟨by rw [iUnion_disjointed,hUnion H hH],?_,?_⟩
    · intro j z hz
      have hR := (disjointed_subset (P H) j hz).1
      exact (openCover_subset_wide_split N (H/C) hR.1).resolve_right hR.2
    · intro j z hz i
      exact mem_iInter.mp (disjointed_subset (P H) j hz).2 i

#print axioms finite_fundamental_partition

end QuantitativeSpectralExceptionalGeometry
