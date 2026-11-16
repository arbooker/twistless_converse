module

public import AsymptoticRegionL2V1
public import Mathlib.Analysis.InnerProductSpace.Subspace

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ)

def region (n : ℤ) : Set α := {x | (n:ℝ)≤l x ∧ l x<(n:ℝ)+1}

theorem region_measurable (hl : Measurable l) (n : ℤ) : MeasurableSet (region l n) :=
  hl measurableSet_Ico

omit [MeasurableSpace α] in
theorem region_disjoint {n m : ℤ} (hnm : n≠m) : Disjoint (region l n) (region l m) := by
  apply Set.disjoint_left.mpr
  intro x hn hm
  obtain h|h := lt_or_gt_of_ne hnm
  · have hcast : (n:ℝ)+1≤(m:ℝ) := by exact_mod_cast h
    linarith [hn.2,hm.1]
  · have hcast : (m:ℝ)+1≤(n:ℝ) := by exact_mod_cast h
    linarith [hm.2,hn.1]

omit [MeasurableSpace α] in
theorem mem_floor_region (x : α) : x∈region l ⌊l x⌋ :=
  ⟨Int.floor_le _,Int.lt_floor_add_one _⟩

variable (hl : Measurable l)

abbrev space (n : ℤ) := AsymptoticRegionL2.Space μ (region l n) (region_measurable l hl n)

def projection (n : ℤ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  AsymptoticRegionL2.projection μ (region l n) (region_measurable l hl n)

theorem projection_coeFn (n : ℤ) (f : Lp ℂ 2 μ) :
    projection μ l hl n f=ᵐ[μ](region l n).indicator f :=
  AsymptoticRegionL2.projection_coeFn μ _ _ f

theorem space_orthogonal :
    OrthogonalFamily ℂ (fun n => ↥(space μ l hl n)) (fun n => (space μ l hl n).subtypeₗᵢ) := by
  intro n m hnm f g
  have hf := (AsymptoticRegionL2.projection_eq_self_iff μ _ _ f.val).mp
    ((AsymptoticRegionL2.mem_space μ _ _ f.val).mp f.property)
  have hg := (AsymptoticRegionL2.projection_eq_self_iff μ _ _ g.val).mp
    ((AsymptoticRegionL2.mem_space μ _ _ g.val).mp g.property)
  change inner ℂ f.val g.val=0
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hf,hg] with x hfx hgx
  change inner ℂ (f.val x) (g.val x)=0
  by_cases hx : x∈region l n
  · have hxm : x∉region l m := fun h => Set.disjoint_left.mp (region_disjoint l hnm) hx h
    rw [hgx hxm,inner_zero_right]
  · rw [hfx hx,inner_zero_left]

theorem projection_sum_norm_square (S : Finset ℤ) (f : Lp ℂ 2 μ) :
    ‖∑ n∈S,projection μ l hl n f‖^2=∑ n∈S,‖projection μ l hl n f‖^2 := by
  let v (n : ℤ) : space μ l hl n := AsymptoticRegionL2.restrict μ _ _ f
  exact (space_orthogonal μ l hl).norm_sum v S

/-- Actual finite orthogonal band projections satisfy the Bessel bound. -/
theorem projection_sum_norm_le (S : Finset ℤ) (f : Lp ℂ 2 μ) :
    ‖∑ n∈S,projection μ l hl n f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have hsum := Lp.coeFn_finsetSum S (fun n => projection μ l hl n f)
  have he : ∀ᵐ x ∂μ,∀ n∈S,projection μ l hl n f x=(region l n).indicator f x := by
    exact (Filter.eventually_all_finite S.finite_toSet).mpr (fun n _ => projection_coeFn μ l hl n f)
  filter_upwards [hsum,he] with x hx he
  rw [hx,Finset.sum_apply]
  have heq : (∑ n∈S,projection μ l hl n f x)=
      if ⌊l x⌋∈S then f x else 0 := by
    classical
    have ht (n : ℤ) (hn : n∈S) : projection μ l hl n f x=if n=⌊l x⌋ then f x else 0 := by
      rw [he n hn]
      by_cases hn0 : n=⌊l x⌋
      · subst n
        simp only [mem_floor_region l x,Set.indicator_of_mem,ite_true]
      · have hx0 : x∉region l n := fun hx0 =>
          Set.disjoint_left.mp (region_disjoint l hn0) hx0 (mem_floor_region l x)
        simp only [Set.indicator_of_notMem hx0,hn0,ite_false]
    rw [Finset.sum_congr rfl ht]
    exact Finset.sum_ite_eq' S _ _
  rw [heq]
  split_ifs <;> simp

theorem sum_projection_norm_square_le (S : Finset ℤ) (f : Lp ℂ 2 μ) :
    (∑ n∈S,‖projection μ l hl n f‖^2)≤‖f‖^2 := by
  rw [←projection_sum_norm_square]
  exact pow_le_pow_left₀ (norm_nonneg _) (projection_sum_norm_le μ l hl S f) 2

#print axioms region_disjoint
#print axioms space_orthogonal
#print axioms projection_sum_norm_square
#print axioms projection_sum_norm_le
#print axioms sum_projection_norm_square_le

end QuantitativeMaass.LogBands
