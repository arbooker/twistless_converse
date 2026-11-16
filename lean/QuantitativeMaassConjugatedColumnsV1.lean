module

public import QuantitativeMaassConjugatedBlocksV1
public import QuantitativeMaassColumnInputTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology BigOperators ENNReal

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

def rowInverseSum (J : ℕ) (n : ℤ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ∑ m∈Finset.Icc (n-(J:ℤ)) (n+(J:ℤ)),inverse μ l hl m

/-- The actual column of a capped conjugation uses only the finite inverse
weight bands that can reach its output point. -/
def conjugatedColumn (c : α → Lp ℂ 2 μ) (J : ℕ) (x : α) : Lp ℂ 2 μ :=
  (rowInverseSum μ l hl J ⌊l x⌋).adjoint ((Real.exp (l x):ℂ) • c x)

theorem conjugatedColumn_inner (c : α → Lp ℂ 2 μ) (J : ℕ) (x : α) (v : Lp ℂ 2 μ) :
    inner ℂ (conjugatedColumn μ l hl c J x) v=
      (Real.exp (l x):ℂ)*inner ℂ (c x) (rowInverseSum μ l hl J ⌊l x⌋ v) := by
  unfold conjugatedColumn
  rw [adjoint_inner_left,inner_smul_left]
  simp only [Complex.conj_ofReal]

/-- A pointwise column representation survives bounded finite-propagation
conjugation on every L2 input, without a global inverse-weight domain assumption. -/
theorem boundedConjugation_column_coeFn (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (c : α → Lp ℂ 2 μ) (hc : ∀ v : Lp ℂ 2 μ,T v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (J : ℕ) (hT : HasBandPropagation μ l hl T J) (v : Lp ℂ 2 μ) :
    boundedConjugation μ l hl T J hT v=ᵐ[μ]
      (fun x => inner ℂ (conjugatedColumn μ l hl c J x) v) := by
  let B := boundedConjugation μ l hl T J hT
  have hn (n : ℤ) : ∀ᵐ x ∂μ,x∈region l n →
      B v x=(Real.exp (l x):ℂ)*inner ℂ (c x) (rowInverseSum μ l hl J n v) := by
    have he : projection μ l hl n (B v)=forward μ l hl n (T (rowInverseSum μ l hl J n v)) := by
      rw [boundedConjugation_row]
      simp only [rowInverseSum,sum_apply,map_sum]
    have hp := projection_coeFn μ l hl n (B v)
    rw [he] at hp
    filter_upwards [hp,forward_coeFn μ l hl n (T (rowInverseSum μ l hl J n v)),
      hc (rowInverseSum μ l hl J n v)] with x hp hf hrep
    intro hx
    rw [Set.indicator_of_mem hx] at hp
    rw [←hp,hf,forwardCoefficient,Set.indicator_of_mem hx,hrep]
  filter_upwards [ae_all_iff.mpr hn] with x hx
  rw [conjugatedColumn_inner]
  exact hx ⌊l x⌋ (mem_floor_region l x)

/-- Exact extended energy trace for the actual weighted operator after
any bounded input map. All columns here are explicitly constructed. -/
theorem boundedConjugation_input_energy_trace {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (basis : HilbertBasis ι ℂ H) (A : H →L[ℂ] Lp ℂ 2 μ)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (c : α → Lp ℂ 2 μ) (hc : ∀ v : Lp ℂ 2 μ,T v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (J : ℕ) (hT : HasBandPropagation μ l hl T J) :
    (∑' i,ENNReal.ofReal (‖boundedConjugation μ l hl T J hT (A (basis i))‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖A.adjoint (conjugatedColumn μ l hl c J x)‖^2) ∂μ :=
  column_input_energy_trace μ basis _ _ (boundedConjugation_column_coeFn μ l hl T c hc J hT) A

#print axioms conjugatedColumn_inner
#print axioms boundedConjugation_column_coeFn
#print axioms boundedConjugation_input_energy_trace

end QuantitativeMaass.LogBands
