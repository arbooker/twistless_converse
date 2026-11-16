module

public import QuantitativeMaassCompletedNewSignMetricV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap AsymptoticClassicalPetersson MeasureTheory
open scoped InnerProduct

namespace QuantitativeMaass

section General
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Gram normalization preserves the exact range of a lower bounded
embedding, not just its closure. -/
theorem normalizedEmbedding_range (R : V →L[ℂ] H) {a : ℝ} (ha : 0<a)
    (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    (QuantitativeHolomorphic.normalizedReconstruction R).range=R.range := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact ⟨QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R) x,rfl⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨((R.adjoint.comp R).comp (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R))) x,
      QuantitativeHolomorphic.normalizedReconstruction_reconstruct R ha hR x⟩

/-- The actual weighted target projection is the cogram of the
normalized embedding. -/
theorem normalizedEmbedding_cogram (R : V →L[ℂ] H) [CompleteSpace R.range]
    {a : ℝ} (ha : 0<a) (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    (QuantitativeHolomorphic.normalizedReconstruction R).comp
      (QuantitativeHolomorphic.normalizedReconstruction R).adjoint=R.range.starProjection := by
  let U := QuantitativeHolomorphic.normalizedReconstruction R
  have hr : U.range=R.range := normalizedEmbedding_range R ha hR
  have hg : U.adjoint.comp U=1 := QuantitativeHolomorphic.normalizedReconstruction_gram R ha hR
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [←hr]
    exact ⟨U.adjoint x,rfl⟩
  · intro y hy
    rw [←hr] at hy
    obtain ⟨z,rfl⟩ := hy
    change inner ℂ (x-U (U.adjoint x)) (U z)=0
    rw [←U.adjoint_inner_left,map_sub]
    have he := congrArg (fun T : V →L[ℂ] V => T (U.adjoint x)) hg
    change U.adjoint (U (U.adjoint x))=U.adjoint x at he
    rw [he,sub_self,inner_zero_left]

/-- This is the compressed Gram inverse formula: two inverse square
roots occur between the embedding and its adjoint. -/
theorem embedding_projection_gram_formula (R : V →L[ℂ] H) [CompleteSpace R.range]
    {a : ℝ} (ha : 0<a) (hR : ∀ x,a*‖x‖^2≤‖R x‖^2) :
    R.range.starProjection=R.comp
      ((QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)).comp
        ((QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)).comp R.adjoint)) := by
  rw [←normalizedEmbedding_cogram R ha hR,QuantitativeHolomorphic.normalizedReconstruction,
    adjoint_comp,(QuantitativeHolomorphic.inverseSqrtCFC_selfAdjoint (R.adjoint.comp R)).adjoint_eq,
    comp_assoc]

/-- The compressed-Gram expression with its source and target types fixed. -/
def embeddingGramProjection (R : V →L[ℂ] H) : H →L[ℂ] H :=
  R.comp ((QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)).comp
    ((QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)).comp R.adjoint))

end General

/-- Orthogonal projection onto the genuine closed weighted new/sign
range. Its closedness is supplied by the proved admissible metric bound. -/
def completedNewSignWeightedProjection (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    Lp ℂ 2 (quotientMeasure 0) →L[ℂ] Lp ℂ 2 (quotientMeasure 0) := by
  let R : completedNewSignSpace N hN.1 χ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
    completedNewSignWeightedEmbedding N hN.1 hε hv χ
  let : CompleteSpace R.range :=
    (completedNewSignWeightedEmbedding_closed N hN hε hv χ hχ).2.completeSpace_coe
  exact R.range.starProjection

theorem completedNewSignWeightedProjection_formula (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    completedNewSignWeightedProjection N hN hε hv χ hχ=
      embeddingGramProjection (V := completedNewSignSpace N hN.1 χ)
        (H := Lp ℂ 2 (quotientMeasure 0)) (completedNewSignWeightedEmbedding N hN.1 hε hv χ) := by
  let R : completedNewSignSpace N hN.1 χ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
    completedNewSignWeightedEmbedding N hN.1 hε hv χ
  let : CompleteSpace R.range :=
    (completedNewSignWeightedEmbedding_closed N hN hε hv χ hχ).2.completeSpace_coe
  obtain ⟨a,ha,hl⟩ := completedNewSignWeightedEmbedding_lower N hN hε hv
  apply embedding_projection_gram_formula
    (V := completedNewSignSpace N hN.1 χ) (H := Lp ℂ 2 (quotientMeasure 0)) R ha
  intro x
  exact hl χ hχ x

#print axioms normalizedEmbedding_range
#print axioms normalizedEmbedding_cogram
#print axioms embedding_projection_gram_formula
#print axioms completedNewSignWeightedProjection_formula

end QuantitativeMaass
