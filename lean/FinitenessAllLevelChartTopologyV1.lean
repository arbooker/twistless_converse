module

public import FinitenessAllLevelFiniteLocusV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelChartTopology

open Complex Set FinitenessAllLevelFredholmReduction

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A locus over a common eigenvalue neighborhood, with its subspace topology. -/
abbrev locus (U : Set ℂ) (R : ℂ → X → Prop) := {t : ℂ × X // t.1 ∈ U ∧ R t.1 t.2}

/-- Exact reconstruction with a continuous linear left inverse gives an
actual homeomorphism of the two loci. No closedness or analytic-space structure
is presumed in this topological statement. -/
def reconstructionHomeomorph (U : Set ℂ) (R : ℂ → X → Prop) (K : ℂ → E → Prop)
    (C : X →L[ℂ] E) (J : ℂ → E →L[ℂ] X) (hJ : ContinuousOn J U)
    (hCJ : ∀ z v, C (J z v) = v)
    (hR : ∀ z ∈ U, ∀ x, R z x ↔ ∃ v, K z v ∧ x = J z v) :
    locus U K ≃ₜ locus U R where
  toFun t := ⟨(t.val.1, J t.val.1 t.val.2), t.property.1,
    (hR _ t.property.1 _).mpr ⟨t.val.2, t.property.2, rfl⟩⟩
  invFun t := ⟨(t.val.1, C t.val.2), t.property.1, by
    obtain ⟨v, hv, he⟩ := (hR _ t.property.1 _).mp t.property.2
    rw [he, hCJ]
    exact hv⟩
  left_inv t := by
    apply Subtype.ext
    exact Prod.ext rfl (hCJ _ _)
  right_inv t := by
    apply Subtype.ext
    change (t.val.1, J t.val.1 (C t.val.2)) = t.val
    apply Prod.ext
    · rfl
    obtain ⟨v, _, he⟩ := (hR _ t.property.1 _).mp t.property.2
    change J t.val.1 (C t.val.2) = t.val.2
    rw [he, hCJ]
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hj : Continuous (fun t : locus U K => J t.val.1) :=
      hJ.comp_continuous (continuous_fst.comp continuous_subtype_val) (fun t => t.property.1)
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (hj.clm_apply (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (C.continuous.comp (continuous_snd.comp continuous_subtype_val))

#print axioms reconstructionHomeomorph

end FinitenessAllLevelChartTopology
