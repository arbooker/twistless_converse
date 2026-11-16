module

public import QuantitativeMaassCylinderCenteredOperatorV1
public import QuantitativeMaassCappedExcessExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass

/-- Finite propagation bounds the actual input heights for every center in
an interval, uniformly in the horizontal coordinate. -/
theorem cylinderRadialKernel_height_support (g : ℝ→ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (a b : ℝ) (z w : ℍ)
    (hz : a≤z.im ∧ z.im≤b) (hw : w∈strip) (hk : radialPoincareKernel 0 g z w≠0) :
    w∈upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R) := by
  have hh : |Real.log w.im-Real.log z.im|≤R :=
    le_of_not_gt (fun hn => hk (cylinderRadialKernel_log_zero g R hR hs z w hn))
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  change w.re∈Icc (0:ℝ) 1 ∧ w.im∈Icc _ _
  refine ⟨⟨hw.1,hw.2.le⟩,?_,?_⟩
  · calc
      _ ≤ z.im*Real.exp (-R) := mul_le_mul_of_nonneg_right hz.1 (Real.exp_pos _).le
      _ = Real.exp (Real.log z.im-R) := by rw [Real.exp_sub,Real.exp_log z.im_pos,Real.exp_neg]; rfl
      _ ≤ Real.exp (Real.log w.im) := Real.exp_le_exp.mpr (by linarith)
      _ = w.im := Real.exp_log w.im_pos
  · calc
      w.im = Real.exp (Real.log w.im) := (Real.exp_log w.im_pos).symm
      _ ≤ Real.exp (Real.log z.im+R) := Real.exp_le_exp.mpr (by linarith)
      _ = z.im*Real.exp R := by rw [Real.exp_add,Real.exp_log z.im_pos]
      _ ≤ _ := mul_le_mul_of_nonneg_right hz.2 (Real.exp_pos _).le

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

/-- The actual uncentered column is fixed by the compact propagated input
rectangle; this is an equality in the cylinder L2 space. -/
theorem cylinderTimeColumn_height_projection {a : ℝ} (ha : 0<a) (b : ℝ)
    (z : ℍ) (hz : a≤z.im ∧ z.im≤b) :
    AsymptoticRegionL2.projection (quotientMeasure 0)
      (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R))
      (upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))).measurableSet
      (cylinderTimeColumn f hc he R hR hs z)=cylinderTimeColumn f hc he R hR hs z := by
  apply (AsymptoticRegionL2.projection_eq_self_iff _ _ _ _).mpr
  have hstrip : ∀ᵐ w ∂quotientMeasure 0,w∈strip := by
    rw [translation_quotient_measure]
    exact ae_restrict_mem strip_measurable
  filter_upwards [hstrip,cylinderAbelColumn_coeFn (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
    (evenCoshLift_support_of_time_support f R hR hs) z] with w hw hcol hwK
  change cylinderTimeColumn f hc he R hR hs z w=_ at hcol
  rw [hcol]
  by_contra hn
  exact hwK (cylinderRadialKernel_height_support _ R hR
    (abelProfile_support _ _ (evenCoshLift_support_of_time_support f R hR hs)) a b z w hz hw hn)

/-- Horizontal mean subtraction preserves the same propagated height
support. No commutation with the Euler filter is assumed. -/
theorem cylinderCenteredTimeColumn_height_projection {a : ℝ} (ha : 0<a) (b : ℝ)
    (z : ℍ) (hz : a≤z.im ∧ z.im≤b) :
    AsymptoticRegionL2.projection (quotientMeasure 0)
      (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R))
      (upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))).measurableSet
      (cylinderCenteredTimeColumn f hc he R hR hs z)=cylinderCenteredTimeColumn f hc he R hR hs z := by
  let P := AsymptoticRegionL2.projection (quotientMeasure 0)
    (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R))
    (upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))).measurableSet
  have hi : IntegrableOn (fun u : ℝ => cylinderTimeColumn f hc he R hR hs (u+ᵥz)) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    apply (cylinderAbelColumn_continuous _ _ R hR _).comp
    apply continuous_induced_rng.mpr
    fun_prop
  change P (cylinderTimeColumn f hc he R hR hs z-
    ∫ u in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (u+ᵥz))=_
  rw [map_sub,←P.integral_comp_comm hi,cylinderTimeColumn_height_projection f hc he R hR hs ha b z hz]
  change _-_=_-_
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  exact cylinderTimeColumn_height_projection f hc he R hR hs ha b (u+ᵥz) (by simpa using hz)

/-- A compact input restriction can be inserted on both sides of any
operator inside the actual retained centered-column trace. -/
theorem centered_column_trace_height_localization {a : ℝ} (ha : 0<a) (b : ℝ)
    (S : Set ℍ) (hS : MeasurableSet S) (hheight : ∀ z∈S,a≤z.im ∧ z.im≤b)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    let P := AsymptoticRegionL2.projection (quotientMeasure 0)
      (upperRectangle 0 1 (a*Real.exp (-R)) (b*Real.exp R))
      (upperRectangle_compact _ _ _ _ (mul_pos ha (Real.exp_pos _))).measurableSet
    columnLinearTrace (volume.restrict S) (cylinderCenteredTimeColumn f hc he R hR hs) T=
      columnLinearTrace (volume.restrict S) (cylinderCenteredTimeColumn f hc he R hR hs)
        (P.comp (T.comp P.adjoint)) := by
  intro P
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS] with z hz
  have hp := cylinderCenteredTimeColumn_height_projection f hc he R hR hs ha b z (hheight z hz)
  have hp' : P.adjoint (cylinderCenteredTimeColumn f hc he R hR hs z)=
      cylinderCenteredTimeColumn f hc he R hR hs z := by
    rw [AsymptoticRegionL2.projection_adjoint]
    exact hp
  change (inner ℂ (T _) _).re=(inner ℂ (P (T (P.adjoint _))) _).re
  rw [←P.adjoint_inner_right,hp']

#print axioms cylinderRadialKernel_height_support
#print axioms cylinderTimeColumn_height_projection
#print axioms cylinderCenteredTimeColumn_height_projection
#print axioms centered_column_trace_height_localization
end QuantitativeMaass
