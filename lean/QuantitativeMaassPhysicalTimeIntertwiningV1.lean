module

public import QuantitativeMaassPhysicalProfileExtensionV1
public import QuantitativeMaassEvenTimeCalculusV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The cosh-coordinate time operator uses only interior physical derivatives
at every nonzero time. -/
theorem coshTimeTest_second_physical (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ)
    (hs : Function.support F ⊆ Iic B) (t : ℝ) (ht : t ≠ 0) :
    deriv (deriv (coshTimeTest F)) t = coshTimeOperator F (Real.cosh t) := by
  have hq : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht
  let b := (1+Real.cosh t)/2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbq : b < Real.cosh t := by dsimp [b]; linarith
  obtain ⟨G,hG,_,hGF⟩ := physicalProfile_exists_extension F hF B hs b hb
  have hlocal : G =ᶠ[𝓝 (Real.cosh t)] F := by
    filter_upwards [Ioi_mem_nhds hbq] with q hq
    exact hGF q hq.le
  have htime : coshTimeTest G =ᶠ[𝓝 t] coshTimeTest F :=
    hlocal.comp_tendsto Real.continuous_cosh.continuousAt
  rw [← htime.deriv.deriv_eq, coshTimeTest_second G hG]
  simp only [coshTimeOperator, hlocal.deriv_eq, hlocal.deriv.deriv_eq]

/-- The physical cosh lift carries the original second time derivative.
Only equality strictly above one is needed by the Abel integral. -/
theorem coshTimeOperator_evenCoshLift (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R)
    (q : ℝ) (hq : 1 < q) :
    coshTimeOperator (evenCoshLift f) q = evenCoshLift (deriv (deriv f)) q := by
  have ht := Real.arcosh_pos hq
  have h := coshTimeTest_second_physical (evenCoshLift f)
    (evenCoshLift_smoothOn f hf he hc) (Real.cosh R)
    (by
      intro x hx
      by_contra hn
      exact hx (evenCoshLift_zero_above f R hR hs x (lt_of_not_ge hn))) (Real.arcosh q) ht.ne'
  have heq : coshTimeTest (evenCoshLift f) = f := funext (evenCoshLift_time f he)
  rw [heq, Real.cosh_arcosh hq.le] at h
  rw [← h]
  simp only [evenCoshLift, evenCoshLift_argument q hq.le]

/-- Exact physical radial differential identity for the actual compact
even time test. The endpoint radial coordinate is handled separately. -/
theorem abelProfile_evenCoshLift_laplacian (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R)
    (q : ℝ) (hq : 1 < q) :
    radialLaplacianProfile (abelProfile (evenCoshLift f)) q =
      (1/4 : ℂ) * abelProfile (evenCoshLift f) q -
        abelProfile (evenCoshLift (deriv (deriv f))) q := by
  rw [abelProfile_laplacian_physical (evenCoshLift f)
    (evenCoshLift_smoothOn f hf he hc) (Real.cosh R)
    (by
      intro x hx
      by_contra hn
      exact hx (evenCoshLift_zero_above f R hR hs x (lt_of_not_ge hn))) q hq,
    abelProfile_congr_above_threshold (coshTimeOperator (evenCoshLift f))
      (evenCoshLift (deriv (deriv f))) 1
      (coshTimeOperator_evenCoshLift f hf he hc R hR hs) q hq.le]

#print axioms coshTimeTest_second_physical
#print axioms coshTimeOperator_evenCoshLift
#print axioms abelProfile_evenCoshLift_laplacian

end QuantitativeMaass
