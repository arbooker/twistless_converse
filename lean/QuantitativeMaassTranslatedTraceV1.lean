module

public import QuantitativeMaassWaveCrossKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- Literal spherical identity of the translated original window square. -/
def translatedWindowIdentity (τ : ℝ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℂ :=
  abelProfile (evenCoshLift (translatedWindowSquare K hc R hR a b τ)) 1

/-- Actual translated original-window kernel along a fixed integral correspondence. -/
def translatedWindowIntegralKernel (τ : ℝ) (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x : ℍ) : ℂ :=
  radialPoincareKernel N (abelProfile (evenCoshLift (translatedWindowSquare K hc R hR a b τ)))
    x (positiveIntegralGL M hM • x)

theorem windowAbelColumn_continuous (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : Continuous (windowAbelColumn N K he hc R hR a b) := by
  unfold windowAbelColumn
  exact oneSidedAbelColumn_continuous N _ _ _ _ _

/-- The actual canonical window columns have the globally valid translated
cross kernel, with support chosen internally from the original test. -/
theorem windowAbelColumn_wave_cross (τ : ℝ) (N : ℕ) [NeZero N]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x y : ℍ) :
    inner ℂ (Wave.shiftedQuotientWave N τ (windowAbelColumn N K he hc R hR a b y))
      (windowAbelColumn N K he hc R hR a b x)=
      radialPoincareKernel N (abelProfile (evenCoshLift (translatedWindowSquare K hc R hR a b τ))) x y := by
  unfold windowAbelColumn
  exact timeSquare_wave_kernel_cross N _ _ _ (symmetricWindowTimeTest_real K he R a b) _ _ _ τ x y

/-- Exact scalar-coset split of the translated kernel. -/
theorem translatedWindowIntegralKernel_split (τ : ℝ) (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (x : ℍ) :
    translatedWindowIntegralKernel τ N M hM K hc R hR a b x=
      (if integralIdentityCoset N M then translatedWindowIdentity τ K hc R hR a b else 0)+
        translatedWindowIntegralRemainder τ N M hM K hc R hR a b x := by
  obtain ⟨B,hB,hs⟩ := translatedWindowSquare_uniform_support K hc
  have hL : 0≤2*(B*R)+|τ| := by positivity
  apply radialIntegralKernel_identity_split N M hM _ (2*(B*R)+|τ|) hL
  exact abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ hL (hs R hR a b τ))

/-- The translated actual correspondence kernel and its nonscalar part
are continuous, hence locally integrable for the actual quotient measure. -/
theorem translatedWindowIntegralKernel_continuous (τ : ℝ) (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Continuous (translatedWindowIntegralKernel τ N M hM K hc R hR a b) ∧
      Continuous (translatedWindowIntegralRemainder τ N M hM K hc R hR a b) := by
  let c := windowAbelColumn N K he hc R hR a b
  let W := Wave.shiftedQuotientWave N τ
  have hc' : Continuous c := windowAbelColumn_continuous N K he hc R hR a b
  have hkfun : translatedWindowIntegralKernel τ N M hM K hc R hR a b=
      (fun x => inner ℂ (W (c (positiveIntegralGL M hM • x))) (c x)) := by
    funext x
    exact (windowAbelColumn_wave_cross τ N K he hc R hR a b x (positiveIntegralGL M hM • x)).symm
  have hk : Continuous (translatedWindowIntegralKernel τ N M hM K hc R hR a b) := by
    rw [hkfun]
    exact (W.continuous.comp (hc'.comp (continuous_const_smul (positiveIntegralGL M hM)))).inner hc'
  refine ⟨hk,?_⟩
  have hh : translatedWindowIntegralRemainder τ N M hM K hc R hR a b=(fun x =>
      translatedWindowIntegralKernel τ N M hM K hc R hR a b x-
        (if integralIdentityCoset N M then translatedWindowIdentity τ K hc R hR a b else 0)) := by
    funext x
    rw [translatedWindowIntegralKernel_split]
    ring
  rw [hh]
  exact hk.sub continuous_const

/-- Exact local correspondence main term with an absolutely integrated error. -/
theorem translatedWindowIntegralKernel_integral_error (τ : ℝ) (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det) (s : Set ℍ) (hs : IsCompact s)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    |(∫ x in s,(translatedWindowIntegralKernel τ N M hM K hc R hR a b x).re ∂quotientMeasure N)-
      (quotientMeasure N).real s*
        (if integralIdentityCoset N M then (translatedWindowIdentity τ K hc R hR a b).re else 0)|≤
      ∫ x in s,‖translatedWindowIntegralRemainder τ N M hM K hc R hR a b x‖ ∂quotientMeasure N := by
  let G := translatedWindowIntegralRemainder τ N M hM K hc R hR a b
  have hG : IntegrableOn G s (quotientMeasure N) :=
    (translatedWindowIntegralKernel_continuous τ N M hM K he hc R hR a b).2.continuousOn.integrableOn_compact hs
  have hh : (fun x => (translatedWindowIntegralKernel τ N M hM K hc R hR a b x).re)=
      (fun x => (if integralIdentityCoset N M then (translatedWindowIdentity τ K hc R hR a b).re else 0)+(G x).re) := by
    funext x
    rw [translatedWindowIntegralKernel_split τ,Complex.add_re]
    split_ifs <;> rfl
  have hGi : IntegrableOn (fun x => (G x).re) s (quotientMeasure N) := hG.re
  have hci : IntegrableOn (fun _ : ℍ => if integralIdentityCoset N M then
      (translatedWindowIdentity τ K hc R hR a b).re else 0) s (quotientMeasure N) := integrable_const _
  rw [hh,integral_add hci hGi,integral_const,
    measureReal_restrict_apply_univ,smul_eq_mul,add_sub_cancel_left]
  calc
    _ ≤ ∫ x in s,‖(G x).re‖ ∂quotientMeasure N := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := (quotientMeasure N).restrict s) (fun x => (G x).re)
    _ ≤ _ := integral_mono hG.re.norm hG.norm
      (fun x => by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (G x))

/-- The signed error from the exact cosine-weighted spherical main term
is negligible for the original literal interval. The oscillating main term
is retained explicitly; no unjustified scalar limit for it is asserted. -/
theorem translatedWindowIntegralKernel_trace_error (τ : ℝ) (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t =>
      ((∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (translatedWindowIntegralKernel τ N M hM K hc (positiveWindowRadius ε t)
          (positiveWindowRadius_pos ε t) t (t+ε t) x).re ∂quotientMeasure N)-
        (quotientMeasure N).real (Metric.closedBall o (positiveWindowRadius ε t))*
          (if integralIdentityCoset N M then (translatedWindowIdentity τ K hc (positiveWindowRadius ε t)
            (positiveWindowRadius_pos ε t) t (t+ε t)).re else 0))/(t*ε t)) atTop (𝓝 0) := by
  have hgeom := translatedWindowIntegralRemainder_interval_negligible τ N M hM K he hc o ε hε hproduct
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hgeom
  filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t ht hp
  rw [sub_zero,Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hp ht.1)]
  exact div_le_div_of_nonneg_right (translatedWindowIntegralKernel_integral_error τ N M hM _
    (isCompact_closedBall o (positiveWindowRadius ε t)) K he hc _
    (positiveWindowRadius_pos ε t) t (t+ε t)) (mul_pos hp ht.1).le

#print axioms windowAbelColumn_continuous
#print axioms windowAbelColumn_wave_cross
#print axioms translatedWindowIntegralKernel_split
#print axioms translatedWindowIntegralKernel_continuous
#print axioms translatedWindowIntegralKernel_integral_error
#print axioms translatedWindowIntegralKernel_trace_error

end QuantitativeMaass
