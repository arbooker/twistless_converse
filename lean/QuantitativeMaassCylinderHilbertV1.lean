module

public import QuantitativeMaassTranslationQuotientV1
public import QuantitativeMaassRadialKernelOperatorV1
public import AsymptoticDecodedQuotientV1
public import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticIntegralSubgroup
open AsymptoticOrbitDecode AsymptoticCongruenceQuotient AsymptoticMassTransport
open scoped Topology

namespace QuantitativeMaass

def cylinderFold (z : ℍ) : ℍ := translationLabel ((-Int.floor z.re:ℤ):ℚ) • z

theorem cylinderFold_eq_label (z : ℍ) : cylinderFold z=foldLabel z 1 • z := by
  simp only [cylinderFold,foldLabel,one_smul,mul_one,Int.cast_neg]

theorem cylinderTranslation_measurable (n : ℤ) :
    Measurable (fun z : ℍ => translationLabel ((-n:ℤ):ℚ) • z) :=
  (AsymptoticRationalBranches.action_continuous (translationLabel ((-n:ℤ):ℚ))).measurable

theorem cylinderTranslationFamily_measurable :
    Measurable (fun p : ℍ×ℤ => translationLabel ((-p.2:ℤ):ℚ) • p.1) := by
  apply measurable_from_prod_countable_left
  intro n
  exact cylinderTranslation_measurable n

theorem cylinderFold_measurable : Measurable cylinderFold := by
  have hf : Measurable (fun z : ℍ => Int.floor z.re) :=
    Int.measurable_floor.comp UpperHalfPlane.continuous_re.measurable
  have hh := cylinderTranslationFamily_measurable.comp (measurable_id.prodMk hf)
  simpa only [Function.comp_def,cylinderFold,id_eq] using! hh

theorem cylinderFold_mem (z : ℍ) : cylinderFold z∈strip := by
  rw [cylinderFold_eq_label]
  exact foldLabel_mem z 1

theorem cylinderFold_self {z : ℍ} (hz : z∈strip) : cylinderFold z=z := by
  rw [cylinderFold_eq_label,foldLabel_self z 1 (by simpa only [one_smul] using hz),one_smul]

theorem cylinderFold_invariant (g : gamma 0) (z : ℍ) : cylinderFold (g.val • z)=cylinderFold z := by
  obtain ⟨n,hn⟩ := gamma_zero_translation g
  rw [hn]
  have he := congrArg (fun a : AsymptoticRationalGroup.Group => a • z)
    (foldLabel_integer z 1 n)
  simpa only [foldLabel,mul_smul,one_smul,mul_one,cylinderFold,Int.cast_neg] using he

/-- Every strip L2 class has an actual measurable periodic representative.
Thus the cylinder Hilbert space is the whole strip L2 space. -/
theorem cylinder_automorphicSpace_eq_top : AutomorphicSpace 0=⊤ := by
  apply top_unique
  intro f _
  let F : ℍ → ℂ := fun z => f (cylinderFold z)
  have he : F=ᵐ[quotientMeasure 0] (f : ℍ → ℂ) := by
    have hs : ∀ᵐ z ∂quotientMeasure 0, z∈strip := by
      rw [translation_quotient_measure]
      exact ae_restrict_mem strip_measurable
    filter_upwards [hs] with z hz
    change f (cylinderFold z)=f z
    rw [cylinderFold_self hz]
  have hF : F∈AutomorphicL2.representatives (gamma 0) (quotientMeasure 0) := by
    refine ⟨(Lp.stronglyMeasurable f).measurable.comp cylinderFold_measurable,?_,
      (Lp.memLp f).ae_eq he.symm⟩
    intro g z
    exact congrArg f (cylinderFold_invariant g z)
  apply (LinearMap.range (AutomorphicL2.embedding (gamma 0) (quotientMeasure 0))).le_topologicalClosure
  refine ⟨⟨F,hF⟩,?_⟩
  apply Lp.ext
  exact hF.2.2.coeFn_toLp.trans he

#print axioms cylinderFold_measurable
#print axioms cylinderFold_invariant
#print axioms cylinder_automorphicSpace_eq_top

end QuantitativeMaass
