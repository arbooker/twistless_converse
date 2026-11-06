module

public import QuantitativeSpectralObservabilityFundamentalFiberV1
public import QuantitativeSpectralObservabilityV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGoodRoot

open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open QuantitativeSpectralObservability AsymptoticCongruenceQuotient
open scoped lp ENNReal

attribute [local instance] Classical.propDecidable

abbrev Space := ℓ²(OrbitGroup,ℂ)

/-- Remove the invariant null set of exceptional roots from an operator family. -/
def family (N : ℕ) (T : ℍ → Space →L[ℂ] Space) (x : ℍ) : Space →L[ℂ] Space :=
  if fundamentalGood N x then T x else 0

theorem family_matrix (N : ℕ) (T : ℍ → Space →L[ℂ] Space) (x : ℍ) (g h : OrbitGroup) :
    matrix (family N T x) g h=if fundamentalGood N x then matrix (T x) g h else 0 := by
  by_cases hx : fundamentalGood N x <;> simp [family,hx,matrix]

theorem family_regular (N : ℕ) (hN : 0<N) (T : ℍ → Space →L[ℂ] Space)
    (hm : ∀ g h, Measurable (fun x => matrix (T x) g h)) (hc : Covariant T) :
    (∀ g h, Measurable (fun x => matrix (family N T x) g h)) ∧ Covariant (family N T) := by
  constructor
  · intro g h
    simp only [family_matrix]
    exact Measurable.ite (fundamentalGood_measurable N hN) (hm g h) measurable_const
  · intro x a g h
    simp only [family_matrix,fundamentalGood_smul_iff]
    by_cases hx : fundamentalGood N x
    · simpa only [ite_eq_left hx] using hc x a g h
    · simp only [ite_eq_right hx]

theorem family_norm (N : ℕ) (T : ℍ → Space →L[ℂ] Space) {M : ℝ}
    (hM : ∀ x, ‖T x‖≤M) (x : ℍ) : ‖family N T x‖≤M := by
  by_cases hx : fundamentalGood N x
  · simpa only [family,ite_eq_left hx] using hM x
  · simp only [family,ite_eq_right hx,norm_zero]
    exact (norm_nonneg _).trans (hM x)

theorem family_trace (N : ℕ) (hN : 0<N) (T : ℍ → Space →L[ℂ] Space) :
    trace volume (family N T)=trace volume T := by
  unfold trace
  apply lintegral_congr_ae
  filter_upwards [fundamentalGood_ae N hN] with x hx
  simp only [family,ite_eq_left hx]

/-- The surviving source is zero at the removed roots, so pointwise
observability on good roots becomes an everywhere statement. -/
def source (N : ℕ) (P : ℍ → Submodule ℂ Space) (x : ℍ) : Submodule ℂ Space :=
  if fundamentalGood N x then P x else ⊥

instance source_complete (N : ℕ) (P : ℍ → Submodule ℂ Space)
    [∀ x, CompleteSpace (P x)] (x : ℍ) : CompleteSpace (source N P x) := by
  have hclosed : IsClosed ((source N P x) : Set Space) := by
    by_cases hx : fundamentalGood N x
    · have he : source N P x=P x := ite_eq_left hx
      rw [he]
      exact (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (P x))).isClosed
    · have he : source N P x=⊥ := ite_eq_right hx
      rw [he]
      exact (completeSpace_coe_iff_isComplete.mp
        (inferInstance : CompleteSpace (⊥ : Submodule ℂ Space))).isClosed
  exact hclosed.completeSpace_coe

theorem source_projection (N : ℕ) (P : ℍ → Submodule ℂ Space)
    [∀ x, CompleteSpace (P x)] (x : ℍ) :
    (source N P x).starProjection=family N (fun y => (P y).starProjection) x := by
  by_cases hx : fundamentalGood N x
  · simp only [source,family,ite_eq_left hx]
  · simp only [source,family,ite_eq_right hx,Submodule.starProjection_bot]

theorem source_trace (N : ℕ) (hN : 0<N) (P : ℍ → Submodule ℂ Space)
    [∀ x, CompleteSpace (P x)] :
    trace volume (fun x => (source N P x).starProjection)=
      trace volume (fun x => (P x).starProjection) := by
  simp only [source_projection]
  exact family_trace N hN _

theorem source_observability (N : ℕ) (P : ℍ → Submodule ℂ Space)
    (B C : ℍ → Space →L[ℂ] Space) (K : ℝ)
    (hobs : ∀ x, fundamentalGood N x → ∀ v∈P x,
      ‖v‖^2≤K*(‖B x v‖^2+‖C x v‖^2)) :
    ∀ x v, v∈source N P x →
      ‖v‖^2≤K*(‖family N B x v‖^2+‖family N C x v‖^2) := by
  intro x v hv
  by_cases hx : fundamentalGood N x
  · simp only [source,ite_eq_left hx] at hv
    simpa only [family,ite_eq_left hx] using hobs x hx v hv
  · have hz : v=0 := by simpa only [source,ite_eq_right hx,Submodule.mem_bot] using hv
    simp only [hz,map_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add,mul_zero,le_refl]

theorem source_map (N : ℕ) (P V : ℍ → Submodule ℂ Space)
    (C : ℍ → Space →L[ℂ] Space)
    (hmap : ∀ x, fundamentalGood N x → ∀ v∈P x, C x v∈V x) :
    ∀ x v, v∈source N P x → family N C x v∈source N V x := by
  intro x v hv
  by_cases hx : fundamentalGood N x
  · simp only [source,ite_eq_left hx] at hv ⊢
    simpa only [family,ite_eq_left hx] using hmap x hx v hv
  · simp only [source,family,ite_eq_right hx,zero_apply,Submodule.zero_mem]

#print axioms family_regular
#print axioms source_trace
#print axioms source_observability
#print axioms source_map

end QuantitativeSpectralExceptionalGoodRoot
