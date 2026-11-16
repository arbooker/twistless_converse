module

public import QuantitativeMaassCylinderColumnContinuityV1
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Continuity of an L2 column family on a compact interval supplies the
absolute integrability needed to interchange its literal kernel pairing. -/
theorem continuous_column_pairing_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] (k : ℝ → α → ℂ)
    (hk : Measurable (Function.uncurry k)) (c : ℝ → Lp ℂ 2 μ)
    (hc : Continuous c) (hrep : ∀ x,c x=ᵐ[μ] k x) (v : Lp ℂ 2 μ) :
    Integrable (fun p : ℝ×α => k p.1 p.2*v p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod μ) := by
  let m := volume.restrict (Icc (0:ℝ) 1)
  let E := fun p : ℝ×α => k p.1 p.2*v p.2
  have hE : Measurable E := hk.mul ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)
  have hL (x : ℝ) : MemLp (k x) 2 μ := (Lp.memLp (c x)).ae_eq (hrep x)
  have hi (x : ℝ) : Integrable (fun y => E (x,y)) μ := (hL x).integrable_mul (Lp.memLp v)
  have hb (x : ℝ) : (∫ y,‖E (x,y)‖ ∂μ)≤‖c x‖^2+‖v‖^2 := by
    have hsq : (∫ y,‖k x y‖^2 ∂μ)=‖c x‖^2 := by
      rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
      exact integral_congr_ae ((hrep x).fun_comp (fun z : ℂ => ‖z‖^2)).symm
    rw [←hsq,AsymptoticL2Multiplier.norm_sq_eq_integral,←integral_add
      (hL x).norm.integrable_sq (Lp.memLp v).norm.integrable_sq]
    apply integral_mono (hi x).norm ((hL x).norm.integrable_sq.add (Lp.memLp v).norm.integrable_sq)
    intro y
    dsimp only [E]
    rw [norm_mul]
    change ‖k x y‖*‖v y‖≤‖k x y‖^2+‖v y‖^2
    nlinarith [sq_nonneg (‖k x y‖-‖v y‖)]
  have hm : Integrable (fun x => ∫ y,‖E (x,y)‖ ∂μ) m := by
    apply ((hc.norm.pow 2).add continuous_const).integrableOn_Icc.mono'
      hE.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    exact hb x
  exact (integrable_prod_iff hE.aestronglyMeasurable).mpr ⟨Eventually.of_forall hi,hm⟩

#print axioms continuous_column_pairing_integrable

end QuantitativeMaass
