module

public import QuantitativeMaassColumnTraceFiniteV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ENNReal

namespace QuantitativeMaass

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure α) (c : α → H) (hc : MemLp c 2 μ)

/-- A square-integrable Hilbert-valued column defines an actual linear
operator into scalar L2 by its pointwise inner products. -/
def finiteEnergyColumnLinear : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (hc.inner_const (𝕜:=ℂ) v).toLp (fun x => inner ℂ (c x) v)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(hc.inner_const (𝕜:=ℂ) (v+w)).coeFn_toLp,
      (hc.inner_const (𝕜:=ℂ) v).coeFn_toLp,(hc.inner_const (𝕜:=ℂ) w).coeFn_toLp,
      Lp.coeFn_add ((hc.inner_const (𝕜:=ℂ) v).toLp _) ((hc.inner_const (𝕜:=ℂ) w).toLp _)]
      with x h1 h2 h3 h4
    simp only [Pi.add_apply] at h4
    rw [h1,h4,h2,h3,inner_add_right]
  map_smul' a v := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(hc.inner_const (𝕜:=ℂ) (a • v)).coeFn_toLp,
      (hc.inner_const (𝕜:=ℂ) v).coeFn_toLp,
      Lp.coeFn_smul a ((hc.inner_const (𝕜:=ℂ) v).toLp _)] with x h1 h2 h3
    simp only [Pi.smul_apply,smul_eq_mul] at h3
    rw [h1,h3,h2,inner_smul_right]

theorem finiteEnergyColumnLinear_bound (v : H) :
    ‖finiteEnergyColumnLinear μ c hc v‖≤‖hc.toLp c‖*‖v‖ := by
  have hh : ‖finiteEnergyColumnLinear μ c hc v‖≤‖v‖*‖hc.toLp c‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hc.inner_const (𝕜:=ℂ) v).coeFn_toLp,hc.coeFn_toLp] with x h1 h2
    change ‖(hc.inner_const (𝕜:=ℂ) v).toLp _ x‖≤‖v‖*‖hc.toLp c x‖
    rw [h1,h2,mul_comm]
    exact norm_inner_le_norm _ _
  simpa only [mul_comm] using hh

def finiteEnergyColumnOperator : H →L[ℂ] Lp ℂ 2 μ :=
  (finiteEnergyColumnLinear μ c hc).mkContinuous ‖hc.toLp c‖ (finiteEnergyColumnLinear_bound μ c hc)

theorem finiteEnergyColumnOperator_coeFn (v : H) :
    finiteEnergyColumnOperator μ c hc v=ᵐ[μ](fun x => inner ℂ (c x) v) :=
  (hc.inner_const (𝕜:=ℂ) v).coeFn_toLp

/-- Exact energy of the constructed operator for any countable Hilbert
basis; this is a finite Hilbert-Schmidt operator by the column L2 hypothesis. -/
theorem finiteEnergyColumnOperator_energy {ι : Type*} [Countable ι] (basis : HilbertBasis ι ℂ H) :
    (∑' i,ENNReal.ofReal (‖finiteEnergyColumnOperator μ c hc (basis i)‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖c x‖^2) ∂μ := by
  let K := finiteEnergyColumnOperator μ c hc
  have hm (i : ι) : AEMeasurable (fun x => ENNReal.ofReal (‖K (basis i) x‖^2)) μ :=
    ((Lp.stronglyMeasurable (K (basis i))).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have hrep : ∀ᵐ x ∂μ,∀ i,K (basis i) x=inner ℂ (c x) (basis i) :=
    ae_all_iff.mpr (fun i => finiteEnergyColumnOperator_coeFn μ c hc (basis i))
  simp_rw [complexLp_norm_square_lintegral]
  rw [←lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [hrep] with x hx
  have hsum : HasSum (fun i => ‖K (basis i) x‖^2) (‖c x‖^2) := by
    simp_rw [hx]
    exact hasSum_inner_norm_sq basis (c x)
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum.summable,hsum.tsum_eq]

theorem finiteEnergyColumnOperator_summable {ι : Type*} [Countable ι] (basis : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖finiteEnergyColumnOperator μ c hc (basis i)‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc
  have ht : (∑' i,ENNReal.ofReal (‖finiteEnergyColumnOperator μ c hc (basis i)‖^2))≠∞ := by
    rw [finiteEnergyColumnOperator_energy μ c hc basis,
      ←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht

#print axioms finiteEnergyColumnLinear_bound
#print axioms finiteEnergyColumnOperator_coeFn
#print axioms finiteEnergyColumnOperator_energy
#print axioms finiteEnergyColumnOperator_summable

end QuantitativeMaass
