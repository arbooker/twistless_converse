module

public import QuantitativeMaassShellSummationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass

/-- A three-part comparison for nonnegative spectral sums. The parts may
meet at an endpoint. Only the interior is required to be finite. -/
theorem spectral_partition_majorant {ι : Type*} (S T U : Set ι)
    (hcover : ∀ i,i∈S ∨ i∈T ∨ i∈U) (hS : S.Finite)
    (f w g h : ι → ℝ) (hf : ∀ i,0≤f i)
    (hw : ∀ i,0≤w i) (hg : ∀ i,0≤g i) (hh : ∀ i,0≤h i)
    (hinside : ∀ i∈S,f i≤w i) (houtside : ∀ i∈T,f i≤g i)
    (hexceptional : ∀ i∈U,f i≤h i)
    (hT : Summable (fun i : T => g i.val))
    (hU : Summable (fun i : U => h i.val)) :
    Summable f ∧ (∑' i,f i)≤(∑' i : S,w i.val)+(∑' i : T,g i.val)+(∑' i : U,h i.val) := by
  classical
  let : Fintype S := hS.fintype
  have hs : Summable (S.indicator w) := summable_subtype_iff_indicator.mp (Summable.of_finite)
  have ht : Summable (T.indicator g) := summable_subtype_iff_indicator.mp hT
  have hu : Summable (U.indicator h) := summable_subtype_iff_indicator.mp hU
  have hmajor := (hs.add ht).add hu
  have hnS (i : ι) : 0≤S.indicator w i := Set.indicator_nonneg (fun j _ => hw j) i
  have hnT (i : ι) : 0≤T.indicator g i := Set.indicator_nonneg (fun j _ => hg j) i
  have hnU (i : ι) : 0≤U.indicator h i := Set.indicator_nonneg (fun j _ => hh j) i
  have hpoint (i : ι) : f i≤S.indicator w i+T.indicator g i+U.indicator h i := by
    rcases hcover i with hi|hi|hi
    · rw [Set.indicator_of_mem hi]
      linarith [hinside i hi,hnT i,hnU i]
    · rw [Set.indicator_of_mem hi]
      linarith [houtside i hi,hnS i,hnU i]
    · rw [Set.indicator_of_mem hi]
      linarith [hexceptional i hi,hnS i,hnT i]
  have hsum : Summable f := Summable.of_nonneg_of_le hf hpoint hmajor
  refine ⟨hsum,?_⟩
  have hb := hsum.tsum_le_tsum hpoint hmajor
  rw [(hs.add ht).tsum_add hu,hs.tsum_add ht,← tsum_subtype,← tsum_subtype,← tsum_subtype] at hb
  exact hb

#print axioms spectral_partition_majorant

end QuantitativeMaass
