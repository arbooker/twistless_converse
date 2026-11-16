module

public import QuantitativeMaassRawMetricSourceV1
public import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns
namespace QuantitativeMaass

/-- Independent families in two distinct eigenspaces remain independent
when combined. No orthonormalization or completeness is required. -/
theorem independent_distinct_eigenfamilies {V α β : Type*}
    [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (v : α→V) (w : β→V) (hv : LinearIndependent ℂ v) (hw : LinearIndependent ℂ w)
    {a b : ℂ} (hab : a≠b) (he : ∀ i,T (v i)=a • v i) (hf : ∀ i,T (w i)=b • w i) :
    LinearIndependent ℂ (Sum.elim v w) := by
  have hspanv : Submodule.span ℂ (range v)≤T.eigenspace a := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (he i)
  have hspanw : Submodule.span ℂ (range w)≤T.eigenspace b := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (hf i)
  exact hv.sum_type hw ((T.eigenspaces_iSupIndep.pairwiseDisjoint hab).mono hspanv hspanw)

namespace RawOriginalWindow
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)
    (t ε : ℝ) (e : Sector N)

/-- The literal original windows of BOTH parities form one independent
family in each root sector. This allows a full canonical trace upper bound,
with each parity recovered afterwards using the known opposite lower bound. -/
theorem windowDatum_both_parities_independent :
    LinearIndependent ℂ (Sum.elim
      (fun p : {p : QuantitativeConcreteGoals.maassWindow N 0 t ε //windowSector A P 0 t ε p=e} =>
        windowDatum A P 0 t ε p.val)
      (fun p : {p : QuantitativeConcreteGoals.maassWindow N 1 t ε //windowSector A P 1 t ε p=e} =>
        windowDatum A P 1 t ε p.val)) := by
  let J := cylinderAutomorphic.comp (fullTerminalTranslationIsometry A (NeZero.pos N) P e)
  apply LinearIndependent.of_comp J.toLinearMap
  have h0 := (J.toLinearMap.linearIndependent_iff_of_injOn J.injective.injOn).mpr
    (windowDatum_sector_independent A P 0 t ε e)
  have h1 := (J.toLinearMap.linearIndependent_iff_of_injOn J.injective.injOn).mpr
    (windowDatum_sector_independent A P 1 t ε e)
  have he (σ : ℕ) (p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //windowSector A P σ t ε p=e}) :
      reflectionIsometry 0 (J (windowDatum A P σ t ε p.val))=
        (-1:ℂ)^σ • J (windowDatum A P σ t ε p.val) := by
    have hr := windowDatum_realizes A P σ t ε p.val
    rw [p.property] at hr
    change reflectionIsometry 0 (cylinderAutomorphic
      (fullTerminalTranslationIsometry A (NeZero.pos N) P e (windowDatum A P σ t ε p.val)))=
        (-1:ℂ)^σ • cylinderAutomorphic
          (fullTerminalTranslationIsometry A (NeZero.pos N) P e (windowDatum A P σ t ε p.val))
    rw [fullTerminalTranslationIsometry_original A (NeZero.pos N) P e
      p.val.val.1 σ p.val.property.2.2 _ hr]
    exact principalEulerCylinder_reflection (NeZero.pos N) A
      (AsymptoticReconstructedCount.parameters A P) p.val.val.1 σ p.val.property.2.2
  have hh := independent_distinct_eigenfamilies (reflectionIsometry 0).toLinearMap _ _ h0 h1
    (by norm_num : (1:ℂ)≠ -1)
    (fun p => by simpa only [pow_zero,Function.comp_apply,LinearIsometry.coe_toLinearMap] using! he 0 p)
    (fun p => by simpa only [pow_one,Function.comp_apply,LinearIsometry.coe_toLinearMap] using! he 1 p)
  convert hh using 1
  funext p
  cases p <;> rfl

#print axioms windowDatum_both_parities_independent
end RawOriginalWindow
#print axioms independent_distinct_eigenfamilies
end QuantitativeMaass
