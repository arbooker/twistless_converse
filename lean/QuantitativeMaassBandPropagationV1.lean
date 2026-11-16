module

public import QuantitativeMaassBandSupportV1
public import Mathlib.Data.Int.Interval

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

/-- Finite propagation expressed by actual orthogonal L2 band blocks. -/
def HasBandPropagation (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ) : Prop :=
  ∀ n m : ℤ,(J:ℤ) < |n-m| → ∀ f : Lp ℂ 2 μ,
    projection μ l hl n (T (projection μ l hl m f))=0

def propagatedSupport (S : Finset ℤ) (J : ℕ) : Finset ℤ :=
  S.biUnion (fun m => Finset.Icc (m-(J:ℤ)) (m+(J:ℤ)))

theorem propagatedSupport_excludes (S : Finset ℤ) (J : ℕ) (n : ℤ)
    (hn : n∉propagatedSupport S J) (m : ℤ) (hm : m∈S) : (J:ℤ) < |n-m| := by
  by_contra h
  have hab := abs_le.mp (le_of_not_gt h)
  apply hn
  exact Finset.mem_biUnion.mpr ⟨m,hm,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩

theorem operator_band_support (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : HasBandPropagation μ l hl T J) (S : Finset ℤ) (f : Lp ℂ 2 μ)
    (hf : ∀ m∉S,projection μ l hl m f=0) :
    ∀ n∉propagatedSupport S J,projection μ l hl n (T f)=0 := by
  intro n hn
  rw [eq_sum_projections μ l hl S f hf,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  exact hT n m (propagatedSupport_excludes S J n hn m hm) f

/-- Finite propagation preserves the dense algebraic band space. -/
theorem operator_mem_finiteBandSpace (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ)
    (hT : HasBandPropagation μ l hl T J) (f : finiteBandSpace μ l hl) :
    T f.val∈finiteBandSpace μ l hl := by
  obtain ⟨S,hS⟩ := finiteBandSpace_support μ l hl f
  exact mem_finiteBandSpace_of_support μ l hl (propagatedSupport S J) (T f.val)
    (operator_band_support μ l hl T J hT S f.val hS)

#print axioms propagatedSupport_excludes
#print axioms operator_band_support
#print axioms operator_mem_finiteBandSpace

end QuantitativeMaass.LogBands
