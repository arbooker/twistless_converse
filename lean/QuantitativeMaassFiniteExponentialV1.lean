module

public import QuantitativeMaassFiniteBandMultiplierV1
public import QuantitativeMaassBandMultipliersV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

omit [MeasurableSpace α] in
theorem exponential_band_bound (s : ℝ) :
    ∀ n : ℤ,∃ C : ℝ,0≤C ∧ ∀ x∈region l n,‖(Real.exp (s*l x):ℂ)‖≤C := by
  intro n
  refine ⟨Real.exp (|s| *(|(n:ℝ)|+1)),(Real.exp_pos _).le,?_⟩
  intro x hx
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hla : |l x|≤|(n:ℝ)|+1 := by
    apply abs_le.mpr
    constructor
    · linarith [hx.1,neg_abs_le (n:ℝ)]
    · linarith [hx.2,le_abs_self (n:ℝ)]
  calc
    s*l x ≤ |s*l x| := le_abs_self _
    _ = |s| *|l x| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hla (abs_nonneg s)

def exponentialEnd (s : ℝ) : finiteBandSpace μ l hl →ₗ[ℂ] finiteBandSpace μ l hl :=
  finiteMultiplierEnd μ l hl (fun x => (Real.exp (s*l x):ℂ))
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hl))).aestronglyMeasurable
    (exponential_band_bound l s)

theorem exponentialEnd_coeFn (s : ℝ) (f : finiteBandSpace μ l hl) :
    (exponentialEnd μ l hl s f).val=ᵐ[μ](fun x => (Real.exp (s*l x):ℂ)*f.val x) :=
  finiteMultiplier_coeFn μ l hl _ _ _ f

theorem exponentialEnd_add (s t : ℝ) (f : finiteBandSpace μ l hl) :
    exponentialEnd μ l hl s (exponentialEnd μ l hl t f)=exponentialEnd μ l hl (s+t) f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [exponentialEnd_coeFn μ l hl s (exponentialEnd μ l hl t f),
    exponentialEnd_coeFn μ l hl t f,exponentialEnd_coeFn μ l hl (s+t) f] with x hs ht hst
  rw [hs,ht,hst,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,←add_mul]

theorem exponentialEnd_zero (f : finiteBandSpace μ l hl) : exponentialEnd μ l hl 0 f=f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [exponentialEnd_coeFn μ l hl 0 f] with x hx
  simpa only [zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul] using hx

theorem exponentialEnd_inverse (s : ℝ) (f : finiteBandSpace μ l hl) :
    exponentialEnd μ l hl s (exponentialEnd μ l hl (-s) f)=f := by
  rw [exponentialEnd_add,add_neg_cancel,exponentialEnd_zero]

/-- Multiplication does not enlarge actual finite band support. -/
theorem exponentialEnd_support (s : ℝ) (f : finiteBandSpace μ l hl) (n : ℤ)
    (hf : projection μ l hl n f.val=0) :
    projection μ l hl n (exponentialEnd μ l hl s f).val=0 := by
  apply (AsymptoticRegionL2.projection_eq_zero_iff μ _ _ _).mpr
  have hz := (AsymptoticRegionL2.projection_eq_zero_iff μ _ _ _).mp hf
  filter_upwards [exponentialEnd_coeFn μ l hl s f,hz] with x hx hz hxn
  rw [hx,hz hxn,mul_zero]

#print axioms exponential_band_bound
#print axioms exponentialEnd_add
#print axioms exponentialEnd_inverse
#print axioms exponentialEnd_support

end QuantitativeMaass.LogBands
