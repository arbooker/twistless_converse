module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace QuantitativeMaass.ZeroWave

abbrev Space : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- Literal translations on the logarithmic height line, constructed by
measure-preserving pullback on actual L² functions. -/
def translation (t : ℝ) : Space →ₗᵢ[ℂ] Space :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ => u+t) (measurePreserving_add_right volume t)

def shift (t : ℝ) : Space →L[ℂ] Space := (translation t).toContinuousLinearMap

theorem shift_ae (t : ℝ) (a : Space) : shift t a =ᵐ[volume] fun u : ℝ => a (u+t) :=
  Lp.coeFn_compMeasurePreserving a (measurePreserving_add_right volume t)

theorem shift_zero (a : Space) : shift 0 a=a := by
  apply Lp.ext
  filter_upwards [shift_ae 0 a] with u hu
  simpa using hu

theorem shift_add (s t : ℝ) (a : Space) : shift (s+t) a=shift s (shift t a) := by
  change Lp.compMeasurePreserving (fun u : ℝ => u+(s+t)) _ a =
    Lp.compMeasurePreserving (fun u : ℝ => u+s) _
      (Lp.compMeasurePreserving (fun u : ℝ => u+t) _ a)
  rw [←Lp.compMeasurePreserving_comp_apply]
  have he : (fun u : ℝ => u+t) ∘ (fun u : ℝ => u+s) = fun u : ℝ => u+(s+t) := by
    funext u
    simp [add_assoc]
  simp only [he]

theorem shift_norm (t : ℝ) (a : Space) : ‖shift t a‖=‖a‖ := (translation t).norm_map a

theorem shift_adjoint (t : ℝ) : (shift t).adjoint=shift (-t) := by
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_left ℂ
  intro b
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hi := (translation t).inner_map_map b (shift (-t) a)
  change inner ℂ (shift t b) (shift t (shift (-t) a))=inner ℂ b (shift (-t) a) at hi
  rw [←shift_add,add_neg_cancel,shift_zero] at hi
  exact hi

/-- Translations vary strongly continuously, proved using continuity of
measure-preserving pullback in L² rather than a spectral theorem. -/
theorem shift_strongContinuous (a : Space) : Continuous (fun t : ℝ => shift t a) := by
  let g : ℝ → C(ℝ,ℝ) := fun t => ⟨fun u => u+t,by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : ℝ × ℝ => z.2+z.1)
    fun_prop
  exact (continuous_const : Continuous (fun _ : ℝ => a)).compMeasurePreservingLp hg
    (fun t => measurePreserving_add_right volume t) (by norm_num)

#print axioms shift_add
#print axioms shift_adjoint
#print axioms shift_strongContinuous

end QuantitativeMaass.ZeroWave
