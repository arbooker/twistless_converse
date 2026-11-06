module

public import FinitenessAllLevelExceptionalScalarV1
public import FinitenessAllLevelLocalDichotomyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing FinitenessAllLevelQuadraticCoordinates
open scoped Topology

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℂ → X → Prop}

/-- A single analytic exception function controls root models throughout
an actual chart. Its zeros have no accumulation inside the chart domain. -/
theorem Presentation.exceptional_rootModels [Countable ι] (c : Presentation ι R)
    (hconn : IsPreconnected c.U) (hne : c.U.Nonempty)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f c.U ∧ (¬ EqOn f 0 c.U) ∧
      (∀ w ∈ c.U, ∀ᶠ z in 𝓝[≠] w, f z ≠ 0) ∧
      ∀ w : c.U, f w ≠ 0 → c.RootModel w := by
  obtain ⟨a, ha, he⟩ := exceptional_scalar c.coefficientFunctions c.openU hconn hne
    c.coefficientFunctions_analytic c.ringIdeal
    (fun z => by rw [c.map_ringIdeal]; exact c.zeroLocus_finite z.property (hf z))
  refine ⟨representative c.U c.coefficientFunctions a,
    representative_analytic _ _ c.coefficientFunctions_analytic _,
    representative_not_identically_zero _ _ ha,
    fun w hw => representative_nonzero_punctured _ hconn c.coefficientFunctions_analytic ha hw,
    fun w hw i => ?_⟩
  obtain ⟨q, hq, hs, hz⟩ := he i
  have haw : evaluation c.U c.coefficientFunctions w a ≠ 0 := by
    change a.val w ≠ 0
    rwa [representative_agrees] at hw
  have hsep := hs w haw
  refine ⟨q, hq, hsep, ?_, fun x hx => eliminant_root_branch c.coefficientFunctions
    c.coefficientFunctions_analytic q w x hsep hx⟩
  intro z v hv
  rw [polynomialEquation_eq]
  apply hz z v
  rw [c.map_ringIdeal]
  exact (c.mem_zeroLocus z v).mpr hv

/-- In a compact subset of the chart only finitely many parameters can
fail the scalar root model. -/
theorem Presentation.finite_exceptional_parameters [Countable ι] (c : Presentation ι R)
    (hconn : IsPreconnected c.U) (hne : c.U.Nonempty)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ c.U) :
    {w : ℂ | w ∈ K ∧ ¬ ∃ hw : w ∈ c.U, c.RootModel ⟨w, hw⟩}.Finite := by
  obtain ⟨f, hfan, hfn, _, hmodels⟩ := c.exceptional_rootModels hconn hne hf
  have hd := (hfan.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn).resolve_left hfn
  have hz : (K \ {w | f w ≠ 0}).Finite :=
    hK.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKU hd)
  apply hz.subset
  intro w hw
  refine ⟨hw.1, ?_⟩
  intro hn
  exact hw.2 ⟨hKU hw.1, hmodels ⟨w, hKU hw.1⟩ hn⟩

/-- Every parameter, including an exceptional one, has a punctured
neighborhood consisting entirely of parameters with root models. -/
theorem Presentation.punctured_rootModels [Countable ι] (c : Presentation ι R)
    (hconn : IsPreconnected c.U)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite)
    {w : ℂ} (hw : w ∈ c.U) :
    ∀ᶠ z in 𝓝[≠] w, ∃ hz : z ∈ c.U, c.RootModel ⟨z, hz⟩ := by
  obtain ⟨f, _, _, hp, hm⟩ := c.exceptional_rootModels hconn ⟨w, hw⟩ hf
  have hU : ∀ᶠ z in 𝓝[≠] w, z ∈ c.U :=
    nhdsWithin_le_nhds (c.openU.mem_nhds hw)
  filter_upwards [hU, hp w hw] with z hz hn
  exact ⟨hz, hm ⟨z, hz⟩ hn⟩

#print axioms Presentation.exceptional_rootModels
#print axioms Presentation.finite_exceptional_parameters
#print axioms Presentation.punctured_rootModels

end FinitenessAllLevelPolynomialPresentation
