module

public import QuantitativeMaassCoverMetricEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory Filter UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
namespace QuantitativeMaass

section General
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem l2Multiplier_inverse (c d : α→ℂ)
    (hc : Measurable c) (hd : Measurable d) {C D : ℝ}
    (hC : ∀ z,‖c z‖≤C) (hD : ∀ z,‖d z‖≤D) (hcd : ∀ z,d z*c z=1)
    (f : Lp ℂ 2 μ) :
    AsymptoticL2Multiplier.operator d hd.aestronglyMeasurable (Eventually.of_forall hD)
      (AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable (Eventually.of_forall hC) f)=f := by
  apply Lp.ext
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn d hd.aestronglyMeasurable (Eventually.of_forall hD)
      (AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable (Eventually.of_forall hC) f),
    AsymptoticL2Multiplier.operator_coeFn c hc.aestronglyMeasurable (Eventually.of_forall hC) f] with z hd' hc'
  rw [hd',hc',←mul_assoc,hcd,one_mul]

def positiveL2MultiplierEquiv (c : α→ℝ) (hc : Measurable c)
    {b B : ℝ} (hb : 0<b) (hbound : ∀ z,b≤c z ∧ c z≤B) : Lp ℂ 2 μ ≃L[ℂ] Lp ℂ 2 μ := by
  let f : α→ℂ := fun z => (c z:ℂ)
  let d : α→ℂ := fun z => ((c z)⁻¹:ℝ)
  have hf : Measurable f := Complex.measurable_ofReal.comp hc
  have hd : Measurable d := Complex.measurable_ofReal.comp hc.inv
  have hpos (z : α) : 0<c z := hb.trans_le (hbound z).1
  have hF (z : α) : ‖f z‖≤B := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos z)]
    exact (hbound z).2
  have hD (z : α) : ‖d z‖≤b⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos z))]
    exact inv_anti₀ hb (hbound z).1
  let T := AsymptoticL2Multiplier.operator f hf.aestronglyMeasurable (Eventually.of_forall hF) (μ:=μ)
  let S := AsymptoticL2Multiplier.operator d hd.aestronglyMeasurable (Eventually.of_forall hD) (μ:=μ)
  exact { toLinearMap := T.toLinearMap
          invFun := S
          left_inv := l2Multiplier_inverse μ f d hf hd hF hD (fun z => by
            dsimp only [f,d];rw [←Complex.ofReal_mul,inv_mul_cancel₀ (hpos z).ne',Complex.ofReal_one])
          right_inv := l2Multiplier_inverse μ d f hd hf hD hF (fun z => by
            dsimp only [f,d];rw [←Complex.ofReal_mul,mul_inv_cancel₀ (hpos z).ne',Complex.ofReal_one])
          continuous_toFun := T.continuous
          continuous_invFun := S.continuous }

theorem positiveL2MultiplierEquiv_coeFn (c : α→ℝ) (hc : Measurable c)
    {b B : ℝ} (hb : 0<b) (hbound : ∀ z,b≤c z ∧ c z≤B) (f : Lp ℂ 2 μ) :
    (positiveL2MultiplierEquiv μ c hc hb hbound f : α→ℂ)=ᵐ[μ]fun z => (c z:ℂ)*f z :=
  AsymptoticL2Multiplier.operator_coeFn (fun z => (c z:ℂ))
    (Complex.measurable_ofReal.comp hc).aestronglyMeasurable
    (Eventually.of_forall (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hb.trans_le (hbound z).1)]
      exact (hbound z).2)) f

theorem positiveL2MultiplierEquiv_norm (c : α→ℝ) (hc : Measurable c)
    {b B : ℝ} (hb : 0<b) (hbound : ∀ z,b≤c z ∧ c z≤B) (hB : 0≤B) :
    ‖(positiveL2MultiplierEquiv μ c hc hb hbound).toContinuousLinearMap‖≤B :=
  AsymptoticL2Multiplier.operator_norm_le (fun z => (c z:ℂ))
    (Complex.measurable_ofReal.comp hc).aestronglyMeasurable hB
    (Eventually.of_forall (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hb.trans_le (hbound z).1)]
      exact (hbound z).2))

theorem positiveL2MultiplierEquiv_symm_norm (c : α→ℝ) (hc : Measurable c)
    {b B : ℝ} (hb : 0<b) (hbound : ∀ z,b≤c z ∧ c z≤B) :
    ‖(positiveL2MultiplierEquiv μ c hc hb hbound).symm.toContinuousLinearMap‖≤b⁻¹ :=
  AsymptoticL2Multiplier.operator_norm_le (fun z => ((c z)⁻¹:ℝ))
    (Complex.measurable_ofReal.comp hc.inv).aestronglyMeasurable (inv_nonneg.mpr hb.le)
    (Eventually.of_forall (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hb.trans_le (hbound z).1))]
      exact inv_anti₀ hb (hbound z).1))
end General

variable {ι : Type*} [Fintype ι] [Nonempty ι] (N : ℕ) (g : ι→quotientNormalizerGroup N)
  {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
  (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)

include hδ hY hν hcover

theorem normalizerCoverMetric_bounds (z : ℍ) :
    Real.sqrt (((Fintype.card ι:ℝ)*quotientWeightBound δ+1)⁻¹)≤normalizerCoverMetric N g δ ν z ∧
      normalizerCoverMetric N g δ ν z≤Real.sqrt ((Fintype.card ι:ℝ)/heightWeightFloor δ ν Y) := by
  have hh := normalizerCoverMetricSquare_bounds N g hδ hY hν hcover z
  exact ⟨Real.sqrt_le_sqrt hh.1,Real.sqrt_le_sqrt hh.2⟩

def normalizerCoverMetricEquiv : Lp ℂ 2 (quotientMeasure 0) ≃L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  positiveL2MultiplierEquiv _ (normalizerCoverMetric N g δ ν) (normalizerCoverMetric_measurable N g δ ν)
    (Real.sqrt_pos.mpr (inv_pos.mpr (by
      have hB := quotientWeightBound_nonneg δ
      have hm : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
      positivity))) (normalizerCoverMetric_bounds N g hδ hY hν hcover)

theorem normalizerCoverMetricEquiv_coeFn (f : Lp ℂ 2 (quotientMeasure 0)) :
    (normalizerCoverMetricEquiv N g hδ hY hν hcover f : ℍ→ℂ)=ᵐ[quotientMeasure 0]
      fun z => (normalizerCoverMetric N g δ ν z:ℂ)*f z :=
  positiveL2MultiplierEquiv_coeFn _ _ _ _ _ f

#print axioms positiveL2MultiplierEquiv
#print axioms positiveL2MultiplierEquiv_coeFn
#print axioms positiveL2MultiplierEquiv_norm
#print axioms positiveL2MultiplierEquiv_symm_norm
#print axioms normalizerCoverMetric_bounds
#print axioms normalizerCoverMetricEquiv_coeFn
end QuantitativeMaass
