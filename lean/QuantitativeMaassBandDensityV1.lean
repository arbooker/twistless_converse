module

public import QuantitativeMaassLogBandsV1
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

/-- All genuine logarithmic bands together detect every L2 vector. -/
theorem projection_separates (f : Lp ℂ 2 μ) (hf : ∀ n,projection μ l hl n f=0) : f=0 := by
  have h : ∀ᵐ x ∂μ,∀ n : ℤ,x∈region l n → f x=0 := by
    apply ae_all_iff.mpr
    intro n
    exact (AsymptoticRegionL2.projection_eq_zero_iff μ _ _ f).mp (hf n)
  apply Lp.ext
  filter_upwards [h,Lp.coeFn_zero ℂ 2 μ] with x hx hz
  exact (hx ⌊l x⌋ (mem_floor_region l x)).trans hz.symm

theorem projection_inner (n : ℤ) (f : Lp ℂ 2 μ) :
    inner ℂ (projection μ l hl n f) f=inner ℂ (projection μ l hl n f) (projection μ l hl n f) := by
  have hp := AsymptoticRegionL2.projection_idempotent μ (region l n) (region_measurable l hl n) f
  have hs := ContinuousLinearMap.adjoint_inner_right (projection μ l hl n) (projection μ l hl n f) f
  have hsa : (projection μ l hl n).adjoint=projection μ l hl n :=
    AsymptoticRegionL2.projection_adjoint μ _ _
  rw [hsa] at hs
  change inner ℂ (projection μ l hl n f) (projection μ l hl n f)=
    inner ℂ (AsymptoticRegionL2.projection μ _ _ (AsymptoticRegionL2.projection μ _ _ f)) f at hs
  rw [hp] at hs
  exact hs.symm

/-- The algebraic span of finitely many actual logarithmic bands is dense.
No regularity or lower bound on the original positive weight is needed. -/
theorem bands_dense : (⨆ n : ℤ,space μ l hl n).topologicalClosure=⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply bot_unique
  intro f hf
  change f=0
  apply projection_separates μ l hl f
  intro n
  have hp : projection μ l hl n f∈space μ l hl n :=
    (AsymptoticRegionL2.mem_space μ _ _ _).mpr
      (AsymptoticRegionL2.projection_idempotent μ _ _ f)
  have hinner := (Submodule.mem_orthogonal _ f).mp hf (projection μ l hl n f)
    ((le_iSup (space μ l hl) n) hp)
  rw [projection_inner μ l hl n f] at hinner
  exact inner_self_eq_zero.mp hinner

#print axioms projection_separates
#print axioms projection_inner
#print axioms bands_dense

end QuantitativeMaass.LogBands
