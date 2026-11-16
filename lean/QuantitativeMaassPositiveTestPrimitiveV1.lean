module

public import QuantitativeMaassAbelDistributionEquationV1
public import QuantitativeMaassWaveTimePrimitiveV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions Interval

namespace QuantitativeMaass

/-- A zero-integral test supported away from time zero has a primitive with
exactly the same support bounds. This is the compact primitive needed in
the derivative-zero distribution argument on the positive half-line. -/
theorem timePrimitive_support_of_integral_zero (φ : ℝ → ℝ)
    (δ R : ℝ) (hδ : 0<δ) (hs : Function.support φ⊆Icc δ R)
    (hz : (∫ t,φ t)=0) : Function.support (Wave.timePrimitive φ)⊆Icc δ R := by
  intro t ht
  have hl : δ≤t := by
    by_contra hn
    have htd : t<δ := lt_of_not_ge hn
    have he : Wave.timePrimitive φ t=0 := by
      change (∫ u in (0:ℝ)..t,φ u)=0
      calc
        _ = ∫ _ in (0:ℝ)..t,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro u hu
          have hud : u<δ := hu.2.trans_lt (max_lt_iff.mpr ⟨hδ,htd⟩)
          by_contra hnφ
          exact (not_le_of_gt hud) (hs hnφ).1
        _ = 0 := by simp
    exact ht he
  refine ⟨hl,?_⟩
  by_contra hn
  have hRt : R<t := lt_of_not_ge hn
  have ht0 : 0≤t := hδ.le.trans hl
  have he : Wave.timePrimitive φ t=0 := by
    change (∫ u in (0:ℝ)..t,φ u)=0
    rw [intervalIntegral.integral_of_le ht0]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hz
    · intro u hu
      by_contra hnφ
      have hsu := hs hnφ
      exact hu ⟨hδ.trans_le hsu.1,hsu.2.trans hRt.le⟩
  exact ht he

theorem timePrimitive_smooth (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Wave.timePrimitive φ) := by
  have hd (t : ℝ) := Wave.timePrimitive_hasDerivAt hφ.continuous t
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt,?_⟩
  have he : deriv (Wave.timePrimitive φ)=φ := funext (fun t => (hd t).deriv)
  rw [he]
  exact hφ

def positiveZeroMeanPrimitive (φ : PositiveSmoothTest) (hz : (∫ t,φ t)=0) :
    PositiveSmoothTest where
  toFun := Wave.timePrimitive (φ : ℝ → ℝ)
  contDiff' := timePrimitive_smooth _ φ.contDiff
  hasCompactSupport' := by
    let I := positiveSmoothTestInterval φ
    have hs := timePrimitive_support_of_integral_zero (φ : ℝ → ℝ) I.left I.right
      I.left_pos (fun t ht => I.subset (subset_tsupport _ ht)) hz
    exact isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_Icc)
  tsupport_subset' := by
    let I := positiveSmoothTestInterval φ
    have hs := timePrimitive_support_of_integral_zero (φ : ℝ → ℝ) I.left I.right
      I.left_pos (fun t ht => I.subset (subset_tsupport _ ht)) hz
    have hc : tsupport (Wave.timePrimitive (φ : ℝ → ℝ))⊆Icc I.left I.right :=
      closure_minimal hs isClosed_Icc
    intro t ht
    exact I.left_pos.trans_le (hc ht).1

theorem positiveZeroMeanPrimitive_deriv (φ : PositiveSmoothTest) (hz : (∫ t,φ t)=0) :
    positiveSmoothTestDeriv (positiveZeroMeanPrimitive φ hz)=φ := by
  ext t
  rw [positiveSmoothTestDeriv_apply]
  exact (Wave.timePrimitive_hasDerivAt φ.continuous t).deriv

#print axioms timePrimitive_support_of_integral_zero
#print axioms positiveZeroMeanPrimitive
#print axioms positiveZeroMeanPrimitive_deriv

end QuantitativeMaass
