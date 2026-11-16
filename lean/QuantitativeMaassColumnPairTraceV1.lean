module

public import QuantitativeMaassColumnLinearTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap

namespace QuantitativeMaass

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem finiteEnergyColumnOperator_add (μ : Measure α) (c d : α→H)
    (hc : MemLp c 2 μ) (hd : MemLp d 2 μ) :
    finiteEnergyColumnOperator μ (fun x => c x+d x) (hc.add hd)=
      finiteEnergyColumnOperator μ c hc+finiteEnergyColumnOperator μ d hd := by
  ext v : 1
  apply Lp.ext
  filter_upwards [finiteEnergyColumnOperator_coeFn μ (fun x => c x+d x) (hc.add hd) v,
    finiteEnergyColumnOperator_coeFn μ c hc v,finiteEnergyColumnOperator_coeFn μ d hd v,
    Lp.coeFn_add (finiteEnergyColumnOperator μ c hc v) (finiteEnergyColumnOperator μ d hd v)]
    with x h1 h2 h3 h4
  change finiteEnergyColumnOperator μ (fun x => c x+d x) (hc.add hd) v x=_
  change (finiteEnergyColumnOperator μ c hc v+finiteEnergyColumnOperator μ d hd v) x=_ at h4
  rw [add_apply,h1,h4]
  simp only [Pi.add_apply,h2,h3,inner_add_left]

omit [CompleteSpace H] in
theorem re_inner_polarization (x y : H) :
    (inner ℂ x y).re=(‖x+y‖^2-‖x‖^2-‖y‖^2)/2 := by
  have hh := norm_add_sq (𝕜 := ℂ) x y
  change ‖x+y‖^2=‖x‖^2+2*(inner ℂ x y).re+‖y‖^2 at hh
  linarith

/-- Mixed column trace, proved by polarization of the exact real energy
formula. This applies to bounded measurable finite-branch coefficients. -/
theorem finiteEnergyColumn_pair_trace {ι : Type*} [Countable ι]
    (μ : Measure α) (c d : α→H) (hc : MemLp c 2 μ) (hd : MemLp d 2 μ)
    (basis : HilbertBasis ι ℂ H) :
    (∑' i,(inner ℂ (finiteEnergyColumnOperator μ c hc (basis i))
      (finiteEnergyColumnOperator μ d hd (basis i))).re)=
      ∫ x,(inner ℂ (c x) (d x)).re ∂μ := by
  have hcS := finiteEnergyColumnOperator_summable μ c hc basis
  have hdS := finiteEnergyColumnOperator_summable μ d hd basis
  have hcdS := finiteEnergyColumnOperator_summable μ (fun x => c x+d x) (hc.add hd) basis
  have hcI := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  have hdI := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hcdI : Integrable (fun x => ‖c x+d x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (hc.add hd).aestronglyMeasurable).mp (hc.add hd)
  have henergy (e : α→H) (he : MemLp e 2 μ) :
      (∑' i,‖finiteEnergyColumnOperator μ e he (basis i)‖^2)=∫ x,‖e x‖^2 ∂μ := by
    simpa only [adjoint_one,one_apply_eq_self] using finiteEnergyColumn_input_real_energy μ e he basis 1
  simp_rw [re_inner_polarization]
  have hadd (i : ι) : finiteEnergyColumnOperator μ c hc (basis i)+
      finiteEnergyColumnOperator μ d hd (basis i)=
      finiteEnergyColumnOperator μ (fun x => c x+d x) (hc.add hd) (basis i) := by
    rw [finiteEnergyColumnOperator_add,add_apply]
  simp_rw [hadd]
  rw [tsum_div_const,(hcdS.sub hcS).tsum_sub hdS,hcdS.tsum_sub hcS,
    henergy (fun x => c x+d x) (hc.add hd),henergy c hc,henergy d hd,integral_div]
  have hsubI : Integrable (fun x => ‖c x+d x‖^2-‖c x‖^2) μ := hcdI.sub hcI
  rw [integral_sub hsubI hdI,integral_sub hcdI hcI]

#print axioms finiteEnergyColumnOperator_add
#print axioms re_inner_polarization
#print axioms finiteEnergyColumn_pair_trace

end QuantitativeMaass
