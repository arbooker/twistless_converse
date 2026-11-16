module

public import QuantitativeMaassBoundedConjugationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem projection_mem_finiteBandSpace (m : ℤ) (f : Lp ℂ 2 μ) :
    projection μ l hl m f∈finiteBandSpace μ l hl := by
  apply le_iSup (space μ l hl) m
  exact (AsymptoticRegionL2.mem_space μ _ _ _).mpr
    (AsymptoticRegionL2.projection_idempotent μ _ _ f)

theorem exponential_neg_one_projection (m : ℤ) (f : Lp ℂ 2 μ) :
    (exponentialEnd μ l hl (-1)
      ⟨projection μ l hl m f,projection_mem_finiteBandSpace μ l hl m f⟩).val=inverse μ l hl m f := by
  classical
  have hs : ∀ n∉({m}:Finset ℤ),projection μ l hl n (projection μ l hl m f)=0 := by
    intro n hn
    have hnm : n≠m := by simpa only [Finset.mem_singleton] using hn
    simp only [projection_projection,hnm,ite_false]
  have h := exponential_neg_one_sum μ l hl {m}
    ⟨projection μ l hl m f,projection_mem_finiteBandSpace μ l hl m f⟩ hs
  simpa only [Finset.sum_singleton,inverse_projection] using h

variable (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ) (hT : HasBandPropagation μ l hl T J)

/-- Every block of the bounded extension agrees with the literal weighted
integral block, even when the full input has no unweighted L2 representative. -/
theorem boundedConjugation_block (n m : ℤ) (f : Lp ℂ 2 μ) :
    projection μ l hl n (boundedConjugation μ l hl T J hT (projection μ l hl m f))=
      forward μ l hl n (T (inverse μ l hl m f)) := by
  let v : finiteBandSpace μ l hl :=
    ⟨projection μ l hl m f,projection_mem_finiteBandSpace μ l hl m f⟩
  rw [show projection μ l hl m f=v.val from rfl,boundedConjugation_on_finite]
  change projection μ l hl n
    (exponentialEnd μ l hl 1 (finitePropagationMap μ l hl T J hT
      (exponentialEnd μ l hl (-1) v))).val=_
  rw [projection_exponential_one]
  change forward μ l hl n (T (exponentialEnd μ l hl (-1) v).val)=_
  rw [exponential_neg_one_projection]

theorem boundedConjugation_band_propagation :
    HasBandPropagation μ l hl (boundedConjugation μ l hl T J hT) J := by
  intro n m hnm f
  rw [boundedConjugation_block]
  exact conjugated_block_zero μ l hl T J hT n m hnm f

/-- The output in one band is an exact finite row for every weighted L2
input. This formula does not require the inverse-weighted full input to lie
in L2, and is the bridge to original polynomial-growth Euler functions. -/
theorem boundedConjugation_row (n : ℤ) (f : Lp ℂ 2 μ) :
    projection μ l hl n (boundedConjugation μ l hl T J hT f)=
      ∑ m∈Finset.Icc (n-(J:ℤ)) (n+(J:ℤ)),forward μ l hl n (T (inverse μ l hl m f)) := by
  classical
  let W := Finset.Icc (n-(J:ℤ)) (n+(J:ℤ))
  let Q : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    ∑ m∈W,(forward μ l hl n).comp (T.comp (inverse μ l hl m))
  let B := boundedConjugation μ l hl T J hT
  have he : (fun g => projection μ l hl n (B g))=(Q : Lp ℂ 2 μ → Lp ℂ 2 μ) := by
    apply (finiteBandSpace_denseRange μ l hl).equalizer
      ((projection μ l hl n).continuous.comp B.continuous) Q.continuous
    funext v
    change projection μ l hl n (B v.val)=Q v.val
    obtain ⟨S,hS⟩ := finiteBandSpace_support μ l hl v
    have hU : ∀ m∉S∪W,projection μ l hl m v.val=0 :=
      fun m hm => hS m (fun h => hm (Finset.mem_union_left W h))
    have hexpand : projection μ l hl n (B v.val)=
        ∑ m∈S∪W,forward μ l hl n (T (inverse μ l hl m v.val)) := by
      conv_lhs => rw [eq_sum_projections μ l hl (S∪W) v.val hU]
      simp only [map_sum,B,boundedConjugation_block]
    rw [hexpand]
    simp only [Q,sum_apply,ContinuousLinearMap.comp_apply]
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro m _ hm
    apply conjugated_block_zero μ l hl T J hT n m _ v.val
    by_contra hh
    have ha := abs_le.mp (le_of_not_gt hh)
    apply hm
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  simpa only [Q,sum_apply,ContinuousLinearMap.comp_apply,W] using congrFun he f

#print axioms projection_mem_finiteBandSpace
#print axioms exponential_neg_one_projection
#print axioms boundedConjugation_block
#print axioms boundedConjugation_band_propagation
#print axioms boundedConjugation_row

end QuantitativeMaass.LogBands
