module

public import QuantitativeMaassFiniteEnergyCompositionV1
public import QuantitativeMaassLinearPacketTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The linear trace density of a square-integrable actual column. -/
def columnLinearTrace (μ : Measure α) (c : α→H) (T : H→L[ℂ]H) : ℝ :=
  ∫ x,(inner ℂ (T (c x)) (c x)).re ∂μ

theorem columnLinearTrace_integrable (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (T : H→L[ℂ]H) : Integrable (fun x => (inner ℂ (T (c x)) (c x)).re) μ := by
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  have ht : AEStronglyMeasurable (fun x => T (c x)) μ :=
    T.continuous.comp_aestronglyMeasurable hc.aestronglyMeasurable
  apply (hi.const_mul ‖T‖).mono'
    (Complex.continuous_re.comp_aestronglyMeasurable (ht.inner hc.aestronglyMeasurable))
  exact Eventually.of_forall (fun x => linearPacketTrace_column_bound T (c x))

theorem columnLinearTrace_bound (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (T : H→L[ℂ]H) : |columnLinearTrace μ c T|≤‖T‖*(∫ x,‖c x‖^2 ∂μ) := by
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  rw [columnLinearTrace,←Real.norm_eq_abs,←integral_const_mul]
  exact norm_integral_le_of_norm_le (hi.const_mul ‖T‖)
    (Eventually.of_forall (fun x => linearPacketTrace_column_bound T (c x)))

theorem columnLinearTrace_sub (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (T S : H→L[ℂ]H) :
    columnLinearTrace μ c (T-S)=columnLinearTrace μ c T-columnLinearTrace μ c S := by
  simp only [columnLinearTrace,sub_apply,inner_sub_left,Complex.sub_re]
  exact integral_sub (columnLinearTrace_integrable μ c hc T) (columnLinearTrace_integrable μ c hc S)

/-- Operator-norm approximation of the actual column trace, requiring no
positivity of the finite-branch approximant. -/
theorem columnLinearTrace_approx (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ)
    (T S : H→L[ℂ]H) {δ : ℝ} (hδ : ‖T-S‖≤δ) :
    |columnLinearTrace μ c T-columnLinearTrace μ c S|≤δ*(∫ x,‖c x‖^2 ∂μ) := by
  rw [←columnLinearTrace_sub μ c hc T S]
  exact (columnLinearTrace_bound μ c hc (T-S)).trans
    (mul_le_mul_of_nonneg_right hδ (integral_nonneg (fun _ => sq_nonneg _)))

variable [CompleteSpace H]

/-- Exact real energy formula after a bounded input map. -/
theorem finiteEnergyColumn_input_real_energy {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ) (basis : HilbertBasis ι ℂ H)
    (F : H→L[ℂ]H) :
    (∑' i,‖finiteEnergyColumnOperator μ c hc (F (basis i))‖^2)=
      ∫ x,‖F.adjoint (c x)‖^2 ∂μ := by
  have hm := finiteEnergyColumn_input_memLp μ c hc F
  have hh := finiteEnergyColumnOperator_energy μ (fun x => F.adjoint (c x)) hm basis
  have hs := finiteEnergyColumnOperator_summable μ (fun x => F.adjoint (c x)) hm basis
  rw [←finiteEnergyColumnOperator_comp μ c hc F] at hh hs
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs,
    ←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))] at hh
  have ht := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),comp_apply] using ht

/-- The linear cogram trace is the genuine filtered Hilbert-Schmidt
energy of the column operator. -/
theorem columnLinearTrace_cogram {ι : Type*} [Countable ι]
    (μ : Measure α) (c : α→H) (hc : MemLp c 2 μ) (basis : HilbertBasis ι ℂ H)
    (F : H→L[ℂ]H) :
    columnLinearTrace μ c (F.comp F.adjoint)=
      ∑' i,‖finiteEnergyColumnOperator μ c hc (F (basis i))‖^2 := by
  rw [finiteEnergyColumn_input_real_energy μ c hc basis F]
  apply integral_congr_ae
  filter_upwards with x
  change (inner ℂ (F (F.adjoint (c x))) (c x)).re=‖F.adjoint (c x)‖^2
  rw [←F.adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

#print axioms columnLinearTrace_integrable
#print axioms columnLinearTrace_bound
#print axioms columnLinearTrace_sub
#print axioms columnLinearTrace_approx
#print axioms finiteEnergyColumn_input_real_energy
#print axioms columnLinearTrace_cogram

end QuantitativeMaass
