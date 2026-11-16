module

public import QuantitativeMaassLogBandsV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory Filter

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

def forwardCoefficient (n : ℤ) : α → ℂ :=
  (region l n).indicator (fun x => (Real.exp (l x):ℂ))

def inverseCoefficient (n : ℤ) : α → ℂ :=
  (region l n).indicator (fun x => (Real.exp (-l x):ℂ))

include hl in
theorem forwardCoefficient_measurable (n : ℤ) : Measurable (forwardCoefficient l n) :=
  (Complex.measurable_ofReal.comp (Real.measurable_exp.comp hl)).indicator (region_measurable l hl n)

include hl in
theorem inverseCoefficient_measurable (n : ℤ) : Measurable (inverseCoefficient l n) :=
  (Complex.measurable_ofReal.comp (Real.measurable_exp.comp hl.neg)).indicator (region_measurable l hl n)

omit [MeasurableSpace α] in
theorem forwardCoefficient_bound (n : ℤ) (x : α) :
    ‖forwardCoefficient l n x‖≤Real.exp ((n:ℝ)+1) := by
  classical
  by_cases hx : x∈region l n
  · rw [forwardCoefficient,Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx.2.le
  · rw [forwardCoefficient,Set.indicator_of_notMem hx,norm_zero]
    exact (Real.exp_pos _).le

omit [MeasurableSpace α] in
theorem inverseCoefficient_bound (n : ℤ) (x : α) :
    ‖inverseCoefficient l n x‖≤Real.exp (-(n:ℝ)) := by
  classical
  by_cases hx : x∈region l n
  · rw [inverseCoefficient,Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (neg_le_neg hx.1)
  · rw [inverseCoefficient,Set.indicator_of_notMem hx,norm_zero]
    exact (Real.exp_pos _).le

def forward (n : ℤ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  AsymptoticL2Multiplier.operator (forwardCoefficient l n)
    (forwardCoefficient_measurable l hl n).aestronglyMeasurable
    (Eventually.of_forall (forwardCoefficient_bound l n))

def inverse (n : ℤ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  AsymptoticL2Multiplier.operator (inverseCoefficient l n)
    (inverseCoefficient_measurable l hl n).aestronglyMeasurable
    (Eventually.of_forall (inverseCoefficient_bound l n))

theorem forward_coeFn (n : ℤ) (f : Lp ℂ 2 μ) :
    forward μ l hl n f=ᵐ[μ](fun x => forwardCoefficient l n x*f x) :=
  AsymptoticL2Multiplier.operator_coeFn _ _ _ f

theorem inverse_coeFn (n : ℤ) (f : Lp ℂ 2 μ) :
    inverse μ l hl n f=ᵐ[μ](fun x => inverseCoefficient l n x*f x) :=
  AsymptoticL2Multiplier.operator_coeFn _ _ _ f

theorem forward_norm_le (n : ℤ) : ‖forward μ l hl n‖≤Real.exp ((n:ℝ)+1) :=
  AsymptoticL2Multiplier.operator_norm_le _ _ (Real.exp_pos _).le _

theorem inverse_norm_le (n : ℤ) : ‖inverse μ l hl n‖≤Real.exp (-(n:ℝ)) :=
  AsymptoticL2Multiplier.operator_norm_le _ _ (Real.exp_pos _).le _

theorem forward_mem_space (n : ℤ) (f : Lp ℂ 2 μ) : forward μ l hl n f∈space μ l hl n := by
  apply (AsymptoticRegionL2.mem_space μ _ _ _).mpr
  apply (AsymptoticRegionL2.projection_eq_self_iff μ _ _ _).mpr
  filter_upwards [forward_coeFn μ l hl n f] with x hx hxn
  rw [hx,forwardCoefficient,Set.indicator_of_notMem hxn,zero_mul]

theorem inverse_mem_space (n : ℤ) (f : Lp ℂ 2 μ) : inverse μ l hl n f∈space μ l hl n := by
  apply (AsymptoticRegionL2.mem_space μ _ _ _).mpr
  apply (AsymptoticRegionL2.projection_eq_self_iff μ _ _ _).mpr
  filter_upwards [inverse_coeFn μ l hl n f] with x hx hxn
  rw [hx,inverseCoefficient,Set.indicator_of_notMem hxn,zero_mul]

/-- Exact cancellation on each actual logarithmic band. -/
theorem forward_inverse (n : ℤ) (f : Lp ℂ 2 μ) :
    forward μ l hl n (inverse μ l hl n f)=projection μ l hl n f := by
  apply Lp.ext
  filter_upwards [forward_coeFn μ l hl n (inverse μ l hl n f),inverse_coeFn μ l hl n f,
    projection_coeFn μ l hl n f] with x hf hi hp
  rw [hf,hi,hp]
  classical
  by_cases hx : x∈region l n
  · simp only [forwardCoefficient,inverseCoefficient,Set.indicator_of_mem hx]
    rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,add_neg_cancel,Real.exp_zero,
      Complex.ofReal_one,one_mul]
  · simp only [forwardCoefficient,inverseCoefficient,Set.indicator_of_notMem hx,zero_mul]

/-- Each actual conjugated block has the sharp band-dependent exponential
bound, before the finite propagation row and column counts are used. -/
theorem conjugated_block_bound (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (n m : ℤ) (f : Lp ℂ 2 μ) :
    ‖forward μ l hl n (T (inverse μ l hl m f))‖≤
      Real.exp ((n:ℝ)+1-(m:ℝ))*‖T‖*‖f‖ := by
  calc
    _ ≤ ‖forward μ l hl n‖*(‖T‖*(‖inverse μ l hl m‖*‖f‖)) := by
      exact ((forward μ l hl n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((T.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((inverse μ l hl m).le_opNorm f) (norm_nonneg T))) (norm_nonneg _))
    _ ≤ Real.exp ((n:ℝ)+1)*(‖T‖*(Real.exp (-(m:ℝ))*‖f‖)) := by
      gcongr
      · exact forward_norm_le μ l hl n
      · exact inverse_norm_le μ l hl m
    _ = _ := by rw [Real.exp_sub,Real.exp_neg]; ring

#print axioms forward_norm_le
#print axioms inverse_norm_le
#print axioms forward_mem_space
#print axioms inverse_mem_space
#print axioms forward_inverse
#print axioms conjugated_block_bound

end QuantitativeMaass.LogBands
