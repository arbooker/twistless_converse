module

public import QuantitativeMaassFiniteEnergyColumnV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

variable {α H G E ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Countable ι]
  (μ : Measure α) (c : α → H) (hc : MemLp c 2 μ)

include hc in
/-- A bounded input map acts on an actual finite-energy column by its
adjoint. Square integrability follows from boundedness. -/
theorem finiteEnergyColumn_input_memLp (A : G →L[ℂ] H) :
    MemLp (fun x => A.adjoint (c x)) 2 μ :=
  hc.continuousLinearMap_comp A.adjoint

theorem finiteEnergyColumnOperator_comp (A : G →L[ℂ] H) :
    (finiteEnergyColumnOperator μ c hc).comp A =
      finiteEnergyColumnOperator μ (fun x => A.adjoint (c x))
        (finiteEnergyColumn_input_memLp μ c hc A) := by
  ext v : 1
  apply Lp.ext
  filter_upwards [finiteEnergyColumnOperator_coeFn μ c hc (A v),
    finiteEnergyColumnOperator_coeFn μ (fun x => A.adjoint (c x))
      (finiteEnergyColumn_input_memLp μ c hc A) v] with x h1 h2
  change finiteEnergyColumnOperator μ c hc (A v) x=_
  rw [h1,h2,A.adjoint_inner_left]

/-- Square summability survives arbitrary bounded input and output maps,
including terminal restriction and the normalized reconstruction inverse. -/
theorem finiteEnergyColumn_composition_summable (basis : HilbertBasis ι ℂ G)
    (A : G →L[ℂ] H) (C : Lp ℂ 2 μ →L[ℂ] E) :
    Summable (fun i => ‖C (finiteEnergyColumnOperator μ c hc (A (basis i)))‖^2) := by
  have hs : Summable (fun i => ‖finiteEnergyColumnOperator μ c hc (A (basis i))‖^2) := by
    have hh := finiteEnergyColumnOperator_summable μ (fun x => A.adjoint (c x))
      (finiteEnergyColumn_input_memLp μ c hc A) basis
    rw [←finiteEnergyColumnOperator_comp μ c hc A] at hh
    exact hh
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs.mul_left (‖C‖^2))
  intro i
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _)
      (C.le_opNorm (finiteEnergyColumnOperator μ c hc (A (basis i)))) 2

/-- The same construction retains its explicit projected-column energy
bound. This estimate is finite, without claiming a sharp Weyl coefficient. -/
theorem finiteEnergyColumn_composition_energy (basis : HilbertBasis ι ℂ G)
    (A : G →L[ℂ] H) (C : Lp ℂ 2 μ →L[ℂ] E) :
    (∑' i,ENNReal.ofReal (‖C (finiteEnergyColumnOperator μ c hc (A (basis i)))‖^2)) ≤
      ENNReal.ofReal (‖C‖^2) *
        ∫⁻ x,ENNReal.ofReal (‖A.adjoint (c x)‖^2) ∂μ := by
  have he := finiteEnergyColumnOperator_energy μ (fun x => A.adjoint (c x))
    (finiteEnergyColumn_input_memLp μ c hc A) basis
  rw [←finiteEnergyColumnOperator_comp μ c hc A] at he
  rw [←he,←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  rw [←ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_pow,ContinuousLinearMap.comp_apply] using
    pow_le_pow_left₀ (norm_nonneg _)
      (C.le_opNorm (finiteEnergyColumnOperator μ c hc (A (basis i)))) 2

#print axioms finiteEnergyColumn_input_memLp
#print axioms finiteEnergyColumnOperator_comp
#print axioms finiteEnergyColumn_composition_summable
#print axioms finiteEnergyColumn_composition_energy

end QuantitativeMaass
