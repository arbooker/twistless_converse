module

public import FinitenessAllLevelPolynomialPresentationV1
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Analytic.Constructions

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℂ → X → Prop}

/-- The finite-coordinate lift has a holomorphic local reading map on the
ambient Banach space. It is constructed by Hahn-Banach extension and a
finite-dimensional inverse, rather than assumed as chart data. -/
theorem Presentation.local_read (c : Presentation ι R) {w : ℂ} (hw : w ∈ c.U) :
    ∃ read : ℂ → X →L[ℂ] (Fin c.n → ℂ), AnalyticAt ℂ read w ∧
      ∀ᶠ z in 𝓝 w, ∀ v, read z (c.lift z v) = v := by
  let E := Fin c.n → ℂ
  let f := c.lift w
  let e := (LinearEquiv.ofInjective f.toLinearMap (c.injective_lift w)).toContinuousLinearEquiv
  obtain ⟨A, hA⟩ := e.symm.toContinuousLinearMap.exist_extension_of_finiteDimensional_range
  have hleft (v : E) : A (f v) = v := by
    calc
      A (f v) = e.symm (e v) := (DFunLike.congr_fun hA (e v)).symm
      _ = v := e.symm_apply_apply v
  let L : ℂ → E →L[ℂ] E := fun z => A.comp (c.lift z)
  have hL : L w = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact hleft v
  have ha : AnalyticAt ℂ L w :=
    ((ContinuousLinearMap.compL ℂ E X E A).analyticAt (c.lift w)).comp (c.analytic_lift w hw)
  have hunit : IsUnit (L w) := by rw [hL]; exact isUnit_one
  have hinv : AnalyticAt ℂ (fun z => Ring.inverse (L z)) w :=
    (analyticOnNhd_inverse (𝕜 := ℂ) (A := E →L[ℂ] E) (L w) hunit).comp ha
  let C : (E →L[ℂ] E) →L[ℂ] (X →L[ℂ] E) :=
    (ContinuousLinearMap.compL ℂ X E E).flip A
  refine ⟨fun z => (Ring.inverse (L z)).comp A,
    (C.analyticAt (Ring.inverse (L w))).comp (f := fun z => Ring.inverse (L z)) hinv, ?_⟩
  have hu : ∀ᶠ z in 𝓝 w, IsUnit (L z) :=
    ha.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds hunit)
  filter_upwards [hu] with z hz v
  change (Ring.inverse (L z) * L z) v = v
  rw [Ring.inverse_mul_cancel _ hz]
  rfl

#print axioms Presentation.local_read

end FinitenessAllLevelPolynomialPresentation
