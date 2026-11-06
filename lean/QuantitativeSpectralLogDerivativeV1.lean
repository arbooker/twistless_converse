module

public import QuantitativeSpectralTraceResolventV1
public import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace QuantitativeSpectralLogDerivative

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- Differentiation of the compact resolvent integral, with concrete local
inverse and path-derivative bounds. The derivative is derived from inverse
calculus; neither differentiability of a logarithm nor a determinant formula
is assumed. -/
theorem hasDerivAt_integral_resolvent {G G' : ℝ → R} {s : ℝ} {S : Set ℝ}
    (hS : S ∈ 𝓝 s) (hG : ∀ x ∈ S, HasDerivAt G (G' x) x)
    (hu : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1+t • (G x-1)))
    {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hR : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, ‖Ring.inverse (1+t • (G x-1))‖ ≤ K)
    (hV : ∀ x ∈ S, ‖G' x‖ ≤ D) :
    HasDerivAt
      (fun x => ∫ t in Icc (0 : ℝ) 1, (G x-1)*Ring.inverse (1+t • (G x-1)))
      (∫ t in Icc (0 : ℝ) 1,
        Ring.inverse (1+t • (G s-1))*G' s*Ring.inverse (1+t • (G s-1))) s := by
  have hs : s ∈ S := mem_of_mem_nhds hS
  have hcont (x : ℝ) (hx : x ∈ S) :
      ContinuousOn (fun t : ℝ => Ring.inverse (1+t • (G x-1))) (Icc 0 1) := by
    intro t ht
    have hi : ContinuousAt Ring.inverse (1+t • (G x-1)) :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (hu x hx t ht).unit).continuousAt
    have ha : ContinuousAt (fun u : ℝ => 1+u • (G x-1)) t := by fun_prop
    exact (hi.comp (f := fun u : ℝ => 1+u • (G x-1)) ha).continuousWithinAt
  have hf (x : ℝ) (hx : x ∈ S) :
      ContinuousOn (fun t : ℝ => (G x-1)*Ring.inverse (1+t • (G x-1))) (Icc 0 1) :=
    continuousOn_const.mul (hcont x hx)
  have hfp : ContinuousOn (fun t : ℝ =>
      Ring.inverse (1+t • (G s-1))*G' s*Ring.inverse (1+t • (G s-1))) (Icc 0 1) :=
    ((hcont s hs).mul continuousOn_const).mul (hcont s hs)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc (0 : ℝ) 1))
    (s := S) (bound := fun _ => K*D*K) hS ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
  · filter_upwards [hS] with x hx
    exact (hf x hx).aestronglyMeasurable measurableSet_Icc
  · exact (hf s hs).integrableOn_Icc
  · exact hfp.aestronglyMeasurable measurableSet_Icc
  · apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht x hx
    exact (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul (hR x hx t ht) (hV x hx)
        (norm_nonneg _) hK)) (hR x hx t ht) (norm_nonneg _) (mul_nonneg hK hD))
  · apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht x hx
    exact QuantitativeSpectralResolventDerivative.hasDerivAt_resolvent_integrand
      (hG x hx) t (hu x hx t ht)

section CStar

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-- The tracial logarithmic derivative for an actual CFC logarithm on a
positive operator path. Local inverse and derivative bounds justify the
integral interchange; cyclicity supplies the inverse-times-derivative formula. -/
theorem hasDerivAt_trace_log {G G' : ℝ → (𝔄)} {s : ℝ} {S : Set ℝ}
    (hS : S ∈ 𝓝 s) (hG : ∀ x ∈ S, HasDerivAt G (G' x) x)
    (hself : ∀ x ∈ S, IsSelfAdjoint (G x))
    (hpos : ∀ x ∈ S, ∀ r ∈ spectrum ℝ (G x), 0 < r)
    {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hR : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, ‖Ring.inverse (1+t • (G x-1))‖ ≤ K)
    (hV : ∀ x ∈ S, ‖G' x‖ ≤ D)
    (τ : (𝔄) →L[ℝ] ℝ)
    (hcyc : ∀ B C, τ (B*C) = τ (C*B)) :
    HasDerivAt (fun x => τ (CFC.log (G x))) (τ (Ring.inverse (G s)*G' s)) s := by
  have hs : s ∈ S := mem_of_mem_nhds hS
  have hu : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1+t • (G x-1)) := by
    intro x hx t ht
    exact QuantitativeSpectralTraceResolvent.affine_isUnit (G x) (hself x hx) (hpos x hx) ht
  have hi := hasDerivAt_integral_resolvent hS hG hu hK hD hR hV
  have hτ := τ.hasFDerivAt.comp_hasDerivAt s hi
  have hd : τ (∫ t in Icc (0 : ℝ) 1,
      Ring.inverse (1+t • (G s-1))*G' s*Ring.inverse (1+t • (G s-1))) =
      τ (Ring.inverse (G s)*G' s) := by
    rw [← τ.integral_comp_comm
      (QuantitativeSpectralTraceResolvent.integrable_resolvent_sandwich
        (G s) (G' s) (hself s hs) (hpos s hs))]
    exact QuantitativeSpectralTraceResolvent.trace_integral_resolvent_sandwich
      (G s) (G' s) (hself s hs) (hpos s hs) τ hcyc
  change HasDerivAt (fun x => τ (∫ t in Icc (0 : ℝ) 1,
    (G x-1)*Ring.inverse (1+t • (G x-1)))) _ s at hτ
  rw [hd] at hτ
  apply hτ.congr_of_eventuallyEq
  filter_upwards [hS] with x hx
  rw [QuantitativeSpectralLogResolvent.operator_log_eq_integral_inverse
    (G x) (hself x hx) (hpos x hx)]

/-- A continuously differentiable positive path needs no separately supplied
resolvent bounds: compactness supplies all bounds required for the tracial
logarithmic derivative. -/
theorem hasDerivAt_trace_log_of_continuous {G G' : ℝ → 𝔄}
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG' : Continuous G')
    (hself : ∀ x, IsSelfAdjoint (G x))
    (hpos : ∀ x, ∀ r ∈ spectrum ℝ (G x), 0 < r)
    (τ : 𝔄 →L[ℝ] ℝ) (hcyc : ∀ B C, τ (B*C) = τ (C*B)) (s : ℝ) :
    HasDerivAt (fun x => τ (CFC.log (G x))) (τ (Ring.inverse (G s)*G' s)) s := by
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  have hr : ContinuousOn (fun p : ℝ × ℝ => Ring.inverse (1+p.2 • (G p.1-1)))
      (Set.Icc (s-1) (s+1) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hi : ContinuousAt Ring.inverse (1+p.2 • (G p.1-1)) :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ)
        (QuantitativeSpectralTraceResolvent.affine_isUnit (G p.1)
          (hself p.1) (hpos p.1) hp.2).unit).continuousAt
    have ha : ContinuousAt (fun q : ℝ × ℝ => 1+q.2 • (G q.1-1)) p := by fun_prop
    exact (hi.comp (f := fun q : ℝ × ℝ => 1+q.2 • (G q.1-1)) ha).continuousWithinAt
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hr
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (s-1) (s+1)) hG'.continuousOn
  apply hasDerivAt_trace_log (S := Ioo (s-1) (s+1))
    (K := max 0 K) (D := max 0 D) (Ioo_mem_nhds (by linarith) (by linarith))
    (fun x _ => hG x) (fun x _ => hself x) (fun x _ => hpos x)
    (le_max_left _ _) (le_max_left _ _) ?_ ?_ τ hcyc
  · intro x hx t ht
    exact (hK (x,t) ⟨⟨hx.1.le,hx.2.le⟩,ht⟩).trans (le_max_right _ _)
  · intro x hx
    exact (hD x ⟨hx.1.le,hx.2.le⟩).trans (le_max_right _ _)

end CStar

#print axioms hasDerivAt_integral_resolvent
#print axioms hasDerivAt_trace_log
#print axioms hasDerivAt_trace_log_of_continuous

end QuantitativeSpectralLogDerivative
