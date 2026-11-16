module

public import QuantitativeHolomorphicRegularClosureV1
public import AsymptoticRegularSignedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch AsymptoticRegularTrace
open scoped ENNReal
namespace QuantitativeMaass.RawCommonReconstruction
open AsymptoticRegularCompactBranch (Space)
open QuantitativeHolomorphic

/-- A bounded measurable local multiplier is a literal identity branch.
Its rooted trace is the corresponding set integral, without a cyclicity
or an infinite ambient trace argument. -/
theorem local_weighted_trace_bound
    (F : ℍ→Space→L[ℂ]Space) (E : ℝ)
    (hweighted : ∀ (B : ℍ→Space→L[ℂ]Space) (L : ℝ),0≤L →
      (∀ a b,Measurable (fun x => matrix (B x) a b)) → Covariant B →
      (∀ x,‖B x‖≤L) → |signedTrace volume (fun x => B x*F x)|≤L*E)
    (S : Set ℍ) (hS : MeasurableSet S) (u : ℍ→ℂ) (hu : Measurable u)
    (L : ℝ) (hL : 0≤L) (hbound : ∀ x,‖u x‖≤L) :
    |∫ x in S,(u x*matrix (F x) 1 1).re|≤L*E := by
  classical
  let b : Branch := {
    label := 1
    coefficient := S.indicator u
    measurable := hu.indicator hS
    bound := L
    bound_nonneg := hL
    norm_le := fun x => by
      by_cases hx : x∈S
      · simpa only [indicator_of_mem hx] using hbound x
      · simpa only [indicator_of_notMem hx,norm_zero] using hL }
  have hn (x : ℍ) : ‖regularSum [b] x‖≤L := by
    simpa only [expressionBound,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      using regularSum_norm_le [b] x
  have hh := hweighted (regularSum [b]) L hL (regularSum_matrix_measurable [b])
    (regularSum_covariant [b]) hn
  have heq : signedTrace volume (fun x => regularSum [b] x*F x)=
      ∫ x in S,(u x*matrix (F x) 1 1).re := by
    unfold signedTrace
    rw [←integral_indicator hS]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change (b.coefficient (1 • x)*(F x (delta 1)) (b.label*1)).re=_
    simp only [b,one_smul,one_mul]
    by_cases hx : x∈S
    · simp only [indicator_of_mem hx,AsymptoticRegularTrace.matrix]
    · simp only [indicator_of_notMem hx,zero_mul,Complex.zero_re]
  rwa [heq] at hh

#print axioms local_weighted_trace_bound
end QuantitativeMaass.RawCommonReconstruction
