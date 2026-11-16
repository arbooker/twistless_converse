module

public import QuantitativeMaassTrimmedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The actual trimmed-window trace of each fixed standard word sum differs
negligibly from its exact cosine-weighted identity term. -/
theorem upperTranslatedWindowKernel_trimmed_trace_error (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0))
    (n : ℕ) (M : HeckeUpper) (hM : 0<M.matrix.det) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (R t),
        (upperTranslatedWindowKernel τ N p K hc (R t) (hRp t)
          (t+δ t) (t+ε t-δ t) n M x).re ∂quotientMeasure N)-
        (Real.sqrt (p:ℝ))⁻¹^n*(HeckeUpper.rawWalks p n M:ℝ)*
          (quotientMeasure N).real (Metric.closedBall o (R t))*
          (translatedWindowIdentity τ K hc (R t) (hRp t) (t+δ t) (t+ε t-δ t)).re)
          /(t*ε t)) atTop (𝓝 0) := by
  let α : ℝ := (Real.sqrt (p:ℝ))⁻¹
  let V := fun t => (quotientMeasure N).real (Metric.closedBall o (R t))
  let I := fun t => (translatedWindowIdentity τ K hc (R t)
    (hRp t) (t+δ t) (t+ε t-δ t)).re
  induction n generalizing M with
  | zero =>
    have hh := translatedWindowIntegralKernel_trimmed_trace_error τ N M.matrix hM K he hc o ε hε δ hδ R hRp hR1 hRlog
    by_cases ht : M.translation
    · simpa only [upperTranslatedWindowKernel,dite_eq_left hM,HeckeUpper.rawWalks,
        ite_eq_left ht,Nat.cast_one,pow_zero,one_mul,integralIdentityCoset_upper_iff N M hM] using hh
    · simpa only [upperTranslatedWindowKernel,dite_eq_left hM,HeckeUpper.rawWalks,
        ite_eq_right ht,Nat.cast_zero,pow_zero,one_mul,mul_zero,zero_mul,sub_zero,
        integralIdentityCoset_upper_iff N M hM] using hh
  | succ n ih =>
    have hi (j : Option (ZMod p)) := ih (HeckeUpper.left p j M) (heckeUpper_left_det_pos p j M hM)
    have hlim := (tendsto_finsetSum Finset.univ (fun j _ => hi j)).const_mul α
    simp only [Finset.sum_const_zero,mul_zero] at hlim
    apply hlim.congr
    intro t
    symm
    rw [upperTranslatedWindowKernel_integral_succ τ N p K he hc _
      (hRp t) (t+δ t) (t+ε t-δ t) n M _ (isCompact_closedBall o (R t))]
    have hmain : α^(n+1)*(HeckeUpper.rawWalks p (n+1) M:ℝ)*V t*I t=
        α*∑ j : Option (ZMod p),α^n*(HeckeUpper.rawWalks p n (HeckeUpper.left p j M):ℝ)*V t*I t := by
      simp only [HeckeUpper.rawWalks,Nat.cast_sum,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    change (α*(∑ j : Option (ZMod p),∫ x in Metric.closedBall o (R t),
      (upperTranslatedWindowKernel τ N p K hc (R t) (hRp t)
        (t+δ t) (t+ε t-δ t) n (HeckeUpper.left p j M) x).re ∂quotientMeasure N)-
      α^(n+1)*(HeckeUpper.rawWalks p (n+1) M:ℝ)*V t*I t)/(t*ε t)=_
    rw [hmain,← Finset.sum_div,Finset.sum_sub_distrib]
    ring

/-- Exact checked tree moments are the identity coefficients of these mixed traces. -/
theorem upperTranslatedWindowKernel_trimmed_root_trace_error (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (R t),
        (upperTranslatedWindowKernel τ N p K hc (R t) (hRp t)
          (t+δ t) (t+ε t-δ t) n HeckeUpper.root x).re ∂quotientMeasure N)-
        (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
          (quotientMeasure N).real (Metric.closedBall o (R t))*
          (translatedWindowIdentity τ K hc (R t) (hRp t) (t+δ t) (t+ε t-δ t)).re)
          /(t*ε t)) atTop (𝓝 0) := by
  have hh := upperTranslatedWindowKernel_trimmed_trace_error τ N p K he hc o ε hε δ hδ R hRp hR1 hRlog n
    HeckeUpper.root (by norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det])
  simpa only [HeckeUpper.rawWalks_root_eq_tree] using hh

/-- Actual mixed wave-Hecke trace error, from the literal trimmed window
and original width hypotheses, around its exact spherical/tree main term. -/
theorem actualMixedHecke_window_trimmed_trace_error (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (δ : ℝ → ℝ) (hδ : ∀ᶠ t in atTop,0≤δ t ∧ 2*δ t≤ε t)
    (R : ℝ → ℝ) (hRp : ∀ t,0<R t)
    (hR1 : ∀ᶠ t in atTop,1≤R t)
    (hRlog : Tendsto (fun t => R t/Real.log t) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (R t),
        (inner ℂ (Wave.shiftedQuotientWave N τ (((HeckeL2.operator N p hN hpN a b hab)^n)
          (windowAbelColumn N K he hc (R t) (hRp t) (t+δ t) (t+ε t-δ t) x)))
          (windowAbelColumn N K he hc (R t) (hRp t) (t+δ t) (t+ε t-δ t) x)).re
        ∂quotientMeasure N)-
        (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
          (quotientMeasure N).real (Metric.closedBall o (R t))*
          (translatedWindowIdentity τ K hc (R t) (hRp t) (t+δ t) (t+ε t-δ t)).re)
          /(t*ε t)) atTop (𝓝 0) := by
  simp_rw [windowAbelColumn_wave_hecke_power τ N p hN hpN hNp a b hab]
  exact upperTranslatedWindowKernel_trimmed_root_trace_error τ N p K he hc o ε hε δ hδ R hRp hR1 hRlog n

#print axioms upperTranslatedWindowKernel_trimmed_trace_error
#print axioms upperTranslatedWindowKernel_trimmed_root_trace_error
#print axioms actualMixedHecke_window_trimmed_trace_error

end QuantitativeMaass
