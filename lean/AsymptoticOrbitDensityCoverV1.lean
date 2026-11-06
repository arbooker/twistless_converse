module

public import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option autoImplicit false
@[expose] public section

namespace AsymptoticOrbitDensity

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]

/-- A normalized nonnegative orbit density has integral bounded by the
measure of any orbit-covering set. Disjointness of translates is not
needed for finiteness. -/
theorem integral_le_cover (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (f : α → ℝ≥0∞) (hf : Measurable f)
    (hn : ∀ x,∑' g : G,f (g • x)=1)
    (s : Set α) (hs : ∀ x,∃ g : G,g • x∈s) :
    (∫⁻ x,f x ∂μ)≤μ s := by
  let : MeasurableConstSMul G α := ⟨fun g => (hmp g).measurable⟩
  have hc : (⋃ g : G,g • s)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨g,hg⟩ := hs x
    apply mem_iUnion.mpr
    refine ⟨g⁻¹,?_⟩
    exact ⟨g • x,hg,inv_smul_smul g x⟩
  calc
    (∫⁻ x,f x ∂μ)=(∫⁻ x in ⋃ g : G,g • s,f x ∂μ) := by rw [hc,Measure.restrict_univ]
    _ ≤ ∑' g : G,∫⁻ x in g • s,f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G,∫⁻ x in s,f (g • x) ∂μ := by
      apply tsum_congr
      intro g
      exact ((hmp g).setLIntegral_comp_emb (measurableEmbedding_const_smul g) f s).symm
    _ = ∫⁻ x in s,∑' g : G,f (g • x) ∂μ :=
      (lintegral_tsum (fun g => (hf.comp (hmp g).measurable).aemeasurable)).symm
    _ = μ s := by simp [hn]

#print axioms integral_le_cover

end AsymptoticOrbitDensity
