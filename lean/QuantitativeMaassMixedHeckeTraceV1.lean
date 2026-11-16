module

public import QuantitativeMaassTranslatedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- Literal finite standard word sum of actual window correspondence kernels.
Nonpositive determinants are extended by zero solely to make the recursion total. -/
def upperTranslatedWindowKernel (τ : ℝ) (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℕ → HeckeUpper → ℍ → ℂ
  | 0,M,x => if hM : 0<M.matrix.det then translatedWindowIntegralKernel τ N M.matrix hM K hc R hR a b x else 0
  | n+1,M,x => (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) *
      ∑ j : Option (ZMod p),upperTranslatedWindowKernel τ N p K hc R hR a b n (HeckeUpper.left p j M) x

/-- Every fixed finite standard word kernel is continuous on the actual
quotient model and is therefore locally integrable. -/
theorem upperTranslatedWindowKernel_continuous (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper) :
    Continuous (upperTranslatedWindowKernel τ N p K hc R hR a b n M) := by
  induction n generalizing M with
  | zero =>
    by_cases hM : 0<M.matrix.det
    · simpa only [upperTranslatedWindowKernel,dite_eq_left hM] using
        (translatedWindowIntegralKernel_continuous τ N M.matrix hM K he hc R hR a b).1
    · simp only [upperTranslatedWindowKernel,dite_eq_right hM]
      exact continuous_const
  | succ n ih =>
    exact (continuous_finsetSum Finset.univ (fun j _ => ih (HeckeUpper.left p j M))).const_mul _

/-- Finite-word integration respects the genuine standard branch recursion. -/
theorem upperTranslatedWindowKernel_integral_succ (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (S : Set ℍ) (hS : IsCompact S) :
    (∫ x in S,(upperTranslatedWindowKernel τ N p K hc R hR a b (n+1) M x).re ∂quotientMeasure N)=
      (Real.sqrt (p:ℝ))⁻¹*∑ j : Option (ZMod p),
        ∫ x in S,(upperTranslatedWindowKernel τ N p K hc R hR a b n (HeckeUpper.left p j M) x).re ∂quotientMeasure N := by
  have hj (j : Option (ZMod p)) : IntegrableOn (fun x =>
      (upperTranslatedWindowKernel τ N p K hc R hR a b n (HeckeUpper.left p j M) x).re) S (quotientMeasure N) :=
    (Complex.continuous_re.comp (upperTranslatedWindowKernel_continuous τ N p K he hc R hR a b n
      (HeckeUpper.left p j M))).continuousOn.integrableOn_compact hS
  simp only [upperTranslatedWindowKernel,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum]
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hj j)]

/-- The original moving-window trace of each fixed standard word sum differs
negligibly from its exact cosine-weighted identity term. -/
theorem upperTranslatedWindowKernel_trace_error (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (n : ℕ) (M : HeckeUpper) (hM : 0<M.matrix.det) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (upperTranslatedWindowKernel τ N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) n M x).re ∂quotientMeasure N)-
        (Real.sqrt (p:ℝ))⁻¹^n*(HeckeUpper.rawWalks p n M:ℝ)*
          (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))*
          (translatedWindowIdentity τ K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t)).re)
          /(t*ε t)) atTop (𝓝 0) := by
  let α : ℝ := (Real.sqrt (p:ℝ))⁻¹
  let V := fun t => (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))
  let I := fun t => (translatedWindowIdentity τ K hc (positiveWindowRadius ε t)
    (positiveWindowRadius_pos ε t) t (t+ε t)).re
  induction n generalizing M with
  | zero =>
    have hh := translatedWindowIntegralKernel_trace_error τ N M.matrix hM K he hc o ε hε hproduct
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
      (positiveWindowRadius_pos ε t) t (t+ε t) n M _ (isCompact_closedBall o (positiveWindowRadius ε t))]
    have hmain : α^(n+1)*(HeckeUpper.rawWalks p (n+1) M:ℝ)*V t*I t=
        α*∑ j : Option (ZMod p),α^n*(HeckeUpper.rawWalks p n (HeckeUpper.left p j M):ℝ)*V t*I t := by
      simp only [HeckeUpper.rawWalks,Nat.cast_sum,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    change (α*(∑ j : Option (ZMod p),∫ x in Metric.closedBall o (positiveWindowRadius ε t),
      (upperTranslatedWindowKernel τ N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
        t (t+ε t) n (HeckeUpper.left p j M) x).re ∂quotientMeasure N)-
      α^(n+1)*(HeckeUpper.rawWalks p (n+1) M:ℝ)*V t*I t)/(t*ε t)=_
    rw [hmain,← Finset.sum_div,Finset.sum_sub_distrib]
    ring

/-- Exact checked tree moments are the identity coefficients of these mixed traces. -/
theorem upperTranslatedWindowKernel_root_trace_error (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (n : ℕ) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (upperTranslatedWindowKernel τ N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) n HeckeUpper.root x).re ∂quotientMeasure N)-
        (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
          (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))*
          (translatedWindowIdentity τ K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t)).re)
          /(t*ε t)) atTop (𝓝 0) := by
  have hh := upperTranslatedWindowKernel_trace_error τ N p K he hc o ε hε hproduct n
    HeckeUpper.root (by norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det])
  simpa only [HeckeUpper.rawWalks_root_eq_tree] using hh

/-- The finite word kernel is exactly the standard iterated correspondence,
with no formal replacement of the geometric branches. -/
theorem upperTranslatedWindowKernel_eq_iterate (τ : ℝ) (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) (x : ℍ) :
    upperTranslatedWindowKernel τ N p K hc R hR a b n M x=
      heckeBranchIterate 1 p n (fun z => radialPoincareKernel N (abelProfile
        (evenCoshLift (translatedWindowSquare K hc R hR a b τ))) x z) (positiveIntegralGL M.matrix hM • x) := by
  induction n generalizing M with
  | zero => simp only [upperTranslatedWindowKernel,dite_eq_left hM,heckeBranchIterate,translatedWindowIntegralKernel]
  | succ n ih =>
    simp only [upperTranslatedWindowKernel,heckeBranchIterate,normalizedCuspHecke,cuspHeckeSum,Complex.real_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih (HeckeUpper.left p j M) (heckeUpper_left_det_pos p j M hM),heckeUpper_left_action]

/-- The mixed finite word kernel is the actual wave-Hecke-power Hilbert kernel. -/
theorem windowAbelColumn_wave_hecke_power (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (u v : ℝ) (n : ℕ) (x : ℍ) :
    inner ℂ (Wave.shiftedQuotientWave N τ
      (((HeckeL2.operator N p hN hpN a b hab)^n) (windowAbelColumn N K he hc R hR u v x)))
      (windowAbelColumn N K he hc R hR u v x)=upperTranslatedWindowKernel τ N p K hc R hR u v n HeckeUpper.root x := by
  rw [upperTranslatedWindowKernel_eq_iterate τ N p K hc R hR u v n HeckeUpper.root
    (by norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det]),heckeUpper_root_action]
  unfold windowAbelColumn
  exact timeSquare_wave_hecke_power_kernel N p hN hpN hNp a b hab _ _ _
    (symmetricWindowTimeTest_real K he R u v) _ _ _ τ n x x

/-- Actual mixed wave-Hecke trace error, from the literal original window
and original width hypotheses, around its exact spherical/tree main term. -/
theorem actualMixedHecke_window_trace_error (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (n : ℕ) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (inner ℂ (Wave.shiftedQuotientWave N τ (((HeckeL2.operator N p hN hpN a b hab)^n)
          (windowAbelColumn N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t) x)))
          (windowAbelColumn N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t) x)).re
        ∂quotientMeasure N)-
        (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
          (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))*
          (translatedWindowIdentity τ K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t)).re)
          /(t*ε t)) atTop (𝓝 0) := by
  simp_rw [windowAbelColumn_wave_hecke_power τ N p hN hpN hNp a b hab]
  exact upperTranslatedWindowKernel_root_trace_error τ N p K he hc o ε hε hproduct n

#print axioms upperTranslatedWindowKernel_continuous
#print axioms upperTranslatedWindowKernel_integral_succ
#print axioms upperTranslatedWindowKernel_trace_error
#print axioms upperTranslatedWindowKernel_root_trace_error
#print axioms upperTranslatedWindowKernel_eq_iterate
#print axioms windowAbelColumn_wave_hecke_power
#print axioms actualMixedHecke_window_trace_error

end QuantitativeMaass
