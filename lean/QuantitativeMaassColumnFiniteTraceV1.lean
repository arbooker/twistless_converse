module

public import QuantitativeMaassColumnPairTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap

namespace QuantitativeMaass

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Every mixed coefficient series of genuine finite-energy column
operators converges absolutely. -/
theorem finiteEnergyColumn_pair_summable {ι : Type*} [Countable ι]
    (μ : Measure α) (c d : α→H) (hc : MemLp c 2 μ) (hd : MemLp d 2 μ)
    (basis : HilbertBasis ι ℂ H) :
    Summable (fun i => (inner ℂ (finiteEnergyColumnOperator μ c hc (basis i))
      (finiteEnergyColumnOperator μ d hd (basis i))).re) := by
  have hcS := finiteEnergyColumnOperator_summable μ c hc basis
  have hdS := finiteEnergyColumnOperator_summable μ d hd basis
  have hcdS := finiteEnergyColumnOperator_summable μ (fun x => c x+d x) (hc.add hd) basis
  have hh := ((hcdS.sub hcS).sub hdS).div_const 2
  have he (i : ι) :
      (inner ℂ (finiteEnergyColumnOperator μ c hc (basis i))
        (finiteEnergyColumnOperator μ d hd (basis i))).re=
      (‖finiteEnergyColumnOperator μ (fun x => c x+d x) (hc.add hd) (basis i)‖^2-
        ‖finiteEnergyColumnOperator μ c hc (basis i)‖^2-
        ‖finiteEnergyColumnOperator μ d hd (basis i)‖^2)/2 := by
    rw [re_inner_polarization,finiteEnergyColumnOperator_add,add_apply]
  simpa only [←he] using hh

/-- A finite sum of actual branch operators has the sum of their mixed
column traces, with the infinite basis sum justified by absolute convergence. -/
theorem finiteEnergyColumn_finset_pair_trace {ι κ : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (d : κ→α→H) (hd : ∀ j,MemLp (d j) 2 μ)
    (basis : HilbertBasis ι ℂ H) (s : Finset κ) :
    (∑' i,(inner ℂ (finiteEnergyColumnOperator μ c hc (basis i))
      ((∑ j∈s,finiteEnergyColumnOperator μ (d j) (hd j)) (basis i))).re)=
      ∑ j∈s,∫ x,(inner ℂ (c x) (d j x)).re ∂μ := by
  classical
  simp only [sum_apply,inner_sum,Complex.re_sum]
  rw [Summable.tsum_finsetSum (fun j _ => finiteEnergyColumn_pair_summable μ c (d j) hc (hd j) basis)]
  apply Finset.sum_congr rfl
  intro j _
  exact finiteEnergyColumn_pair_trace μ c (d j) hc (hd j) basis

#print axioms finiteEnergyColumn_pair_summable
#print axioms finiteEnergyColumn_finset_pair_trace

end QuantitativeMaass
