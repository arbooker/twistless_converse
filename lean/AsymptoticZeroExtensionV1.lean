module

public import AsymptoticL2MultiplierV1
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
@[expose] public section

namespace AsymptoticZeroExtension

open MeasureTheory Set Filter

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) (hs : MeasurableSet s)

include hs in
theorem memLp (f : Lp ℂ 2 (μ.restrict s)) : MemLp (s.indicator f) 2 μ :=
  (memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)

/-- Extension by zero from a measurable region is linear on L² classes. -/
noncomputable def linear : Lp ℂ 2 (μ.restrict s) →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp μ s hs f).toLp (s.indicator f)
  map_add' f g := by
    apply Lp.ext
    have ha := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_add f g)
    filter_upwards [MemLp.coeFn_toLp (memLp μ s hs (f+g)),
      MemLp.coeFn_toLp (memLp μ s hs f),MemLp.coeFn_toLp (memLp μ s hs g),ha,
      Lp.coeFn_add ((memLp μ s hs f).toLp _) ((memLp μ s hs g).toLp _)]
      with x hfg hf hg hsum hadd
    rw [hfg,hadd]
    change s.indicator (f+g) x=(memLp μ s hs f).toLp _ x+(memLp μ s hs g).toLp _ x
    rw [hf,hg,hsum]
    classical
    by_cases hx : x∈s <;> simp [hx]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    have ha := (ae_eq_restrict_iff_indicator_ae_eq hs).mp (Lp.coeFn_smul c f)
    filter_upwards [MemLp.coeFn_toLp (memLp μ s hs (c • f)),
      MemLp.coeFn_toLp (memLp μ s hs f),ha,
      Lp.coeFn_smul c ((memLp μ s hs f).toLp _)] with x hcf hf hsm hadd
    rw [hcf,hadd]
    change s.indicator (c • f) x=c*(memLp μ s hs f).toLp _ x
    rw [hf,hsm]
    classical
    by_cases hx : x∈s <;> simp [hx]

theorem linear_coeFn (f : Lp ℂ 2 (μ.restrict s)) : linear μ s hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp (memLp μ s hs f)

theorem linear_norm (f : Lp ℂ 2 (μ.restrict s)) : ‖linear μ s hs f‖=‖f‖ := by
  change ‖(memLp μ s hs f).toLp (s.indicator f)‖=‖f‖
  rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_indicator_eq_eLpNorm_restrict hs]

noncomputable def isometry : Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  { linear μ s hs with norm_map' := linear_norm μ s hs }

theorem isometry_coeFn (f : Lp ℂ 2 (μ.restrict s)) :
    isometry μ s hs f =ᵐ[μ] s.indicator f := linear_coeFn μ s hs f

#print axioms linear_norm
#print axioms isometry_coeFn

end AsymptoticZeroExtension
