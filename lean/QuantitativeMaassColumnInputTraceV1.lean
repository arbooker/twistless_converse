module

public import QuantitativeMaassAbelEnergyTraceV1
public import QuantitativeMaassHilbertSchmidtIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ENNReal

namespace QuantitativeMaass

/-- Extended square-energy formula without a finite-volume assumption. -/
theorem complexLp_norm_square_lintegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (v : Lp ℂ 2 μ) :
    ENNReal.ofReal (‖v‖^2)=∫⁻ x,ENNReal.ofReal (‖v x‖^2) ∂μ := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v)
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  exact ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))

/-- Exact column formula after an arbitrary bounded input map. This is an
extended nonnegative identity; no trace finiteness is assumed. -/
theorem column_input_energy_trace {α H ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (μ : Measure α) (basis : HilbertBasis ι ℂ H)
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ,K v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (A : H →L[ℂ] Lp ℂ 2 μ) :
    (∑' i,ENNReal.ofReal (‖K (A (basis i))‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖A.adjoint (c x)‖^2) ∂μ := by
  have hm (i : ι) : AEMeasurable (fun x => ENNReal.ofReal (‖K (A (basis i)) x‖^2)) μ :=
    ((Lp.stronglyMeasurable (K (A (basis i)))).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have hrep : ∀ᵐ x ∂μ,∀ i,K (A (basis i)) x=inner ℂ (c x) (A (basis i)) :=
    ae_all_iff.mpr (fun i => hc (A (basis i)))
  simp_rw [complexLp_norm_square_lintegral]
  rw [←lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [hrep] with x hx
  have hsum : HasSum (fun i => ‖K (A (basis i)) x‖^2) (‖A.adjoint (c x)‖^2) := by
    simp_rw [hx,←A.adjoint_inner_left]
    exact hasSum_inner_norm_sq basis (A.adjoint (c x))
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum.summable,hsum.tsum_eq]

#print axioms complexLp_norm_square_lintegral
#print axioms column_input_energy_trace

end QuantitativeMaass
