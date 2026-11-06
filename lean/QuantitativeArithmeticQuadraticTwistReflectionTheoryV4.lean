module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticMellinScaleV1

/-! Consolidated chapter: QuantitativeArithmeticQuadraticTwistReflection. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticQuadraticTwistReflectionMellinV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticTwistReflection
open Complex MeasureTheory FinitenessAllLevelAxisDecay

/-- Unscaling a Mellin functional equation produces its exact entire
conductor factor, with the same sign. -/
theorem unscaled_reflection {N k : ℕ} (hN : 0<N) (a : ℕ → ℂ) (ε : ℂ)
    (h : ∀ s : ℂ, mellin (axis N a) s=ε*mellin (axis N a) ((k:ℂ)-s)) (s : ℂ) :
    mellin (axis 1 a) s=ε*(Real.sqrt N:ℂ)^((k:ℂ)-2*s)*
      mellin (axis 1 a) ((k:ℂ)-s) := by
  have hn : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (show (0:ℝ)<N by exact_mod_cast hN)).ne'
  have hp : (Real.sqrt N:ℂ)^((k:ℂ)-2*s)*(Real.sqrt N:ℂ)^(-((k:ℂ)-s))=
      (Real.sqrt N:ℂ)^(-s) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    ring
  calc
    mellin (axis 1 a) s=(Real.sqrt N:ℂ)^(-s)*(ε*mellin (axis N a) ((k:ℂ)-s)) := by
      rw [QuantitativeArithmeticMellinScale.mellin_one_scale hN,h]
    _=ε*((Real.sqrt N:ℂ)^((k:ℂ)-2*s)*(Real.sqrt N:ℂ)^(-((k:ℂ)-s)))*
        mellin (axis N a) ((k:ℂ)-s) := by rw [hp]; ring
    _=ε*(Real.sqrt N:ℂ)^((k:ℂ)-2*s)*mellin (axis 1 a) ((k:ℂ)-s) := by
      rw [QuantitativeArithmeticMellinScale.mellin_one_scale hN]
      ring

#print axioms unscaled_reflection
end QuantitativeArithmeticQuadraticTwistReflection
end
end

/-! ## QuantitativeArithmeticQuadraticTwistReflectionNormalFormV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticTwistReflection
open Complex Filter Set
open scoped Topology

/-- A punctured-germ representative of a reflected quotient inherits the
functional equation exactly when chosen in meromorphic normal form. -/
theorem normal_form_reflection (F G a : ℂ → ℂ) (K : ℂ)
    (hG : ∀ x, MeromorphicNFAt G x) (ha : ∀ x, AnalyticAt ℂ a x)
    (ha0 : ∀ x, a x≠0) (hgerm : ∀ x, G=ᶠ[𝓝[≠] x] F)
    (he : ∀ z, F z=a z*F (K-z)) :
    ∀ x, G x=a x*G (K-x) := by
  intro x
  have hd : HasDerivAt (fun z : ℂ => K-z) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub K
  have href := hd.tendsto_nhdsNE (by norm_num : (-1:ℂ)≠0)
  have hh : G=ᶠ[𝓝[≠] x] (fun z => a z*G (K-z)) := by
    filter_upwards [hgerm x,(hgerm (K-x)).comp_tendsto href] with z hz hr
    change G (K-z)=F (K-z) at hr
    rw [hz,he,hr]
  have hcomp : MeromorphicNFAt (fun z => G (K-z)) x :=
    (hG (K-x)).comp_analyticAt (analyticAt_const.sub analyticAt_id)
  have hprod : MeromorphicNFAt (fun z => a z*G (K-z)) x :=
    (meromorphicNFAt_mul_iff_right (ha x) (ha0 x)).mpr hcomp
  exact (((hG x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hprod).mp hh).eq_of_nhds

#print axioms normal_form_reflection
end QuantitativeArithmeticQuadraticTwistReflection
end
end
