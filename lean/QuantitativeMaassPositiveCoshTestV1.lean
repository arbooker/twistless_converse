module

public import QuantitativeMaassPositiveTimeTestV1
public import QuantitativeMaassAbelAboveOneCongruenceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

def positiveCoshTest (G : ℝ → ℂ) (t : ℝ) : ℂ := if 0<t then G (Real.cosh t) else 0

theorem positiveCoshTest_zero_below (G : ℝ → ℂ) (δ : ℝ) (hδ : 0<δ)
    (hz : ∀ q∈Icc 1 (Real.cosh δ),G q=0) (t : ℝ) (ht : t<δ) : positiveCoshTest G t=0 := by
  by_cases ht0 : 0<t
  · rw [positiveCoshTest,ite_eq_left ht0]
    apply hz
    refine ⟨Real.one_le_cosh t,?_⟩
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_pos ht0,abs_of_pos hδ] using ht.le
  · exact ite_eq_right ht0

theorem positiveCoshTest_smooth (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (δ : ℝ) (hδ : 0<δ) (hz : ∀ q∈Icc 1 (Real.cosh δ),G q=0) :
    ContDiff ℝ ∞ (positiveCoshTest G) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : 0<t
  · have he : positiveCoshTest G=ᶠ[𝓝 t] (fun s => G (Real.cosh s)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact ite_eq_left hs
    exact (hG.comp Real.contDiff_cosh).contDiffAt.congr_of_eventuallyEq he
  · have htδ : t<δ := lt_of_le_of_lt (le_of_not_gt ht) hδ
    have he : positiveCoshTest G=ᶠ[𝓝 t] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds htδ] with s hs
      exact positiveCoshTest_zero_below G δ hδ hz s hs
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem positiveCoshTest_support (G : ℝ → ℂ) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hz : ∀ q∈Icc 1 (Real.cosh δ),G q=0) (hs : Function.support G⊆Iic (Real.cosh R)) :
    Function.support (positiveCoshTest G)⊆Icc δ R := by
  intro t ht
  change positiveCoshTest G t≠0 at ht
  have ht0 : 0<t := by
    by_contra hn
    exact ht (ite_eq_right hn)
  constructor
  · by_contra hn
    exact ht (positiveCoshTest_zero_below G δ hδ hz t (lt_of_not_ge hn))
  · have hn : G (Real.cosh t)≠0 := by simpa only [positiveCoshTest,ite_eq_left ht0] using ht
    have h := Real.cosh_le_cosh.mp (hs hn)
    simpa only [abs_of_pos ht0,abs_of_nonneg hR] using h

/-- A real q-test vanishing near one gives a genuine positive-time test. -/
def positiveTimeTestOfCosh (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hr : ∀ q,star (G q)=G q) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hz : ∀ q∈Icc 1 (Real.cosh δ),G q=0) (hs : Function.support G⊆Iic (Real.cosh R)) :
    PositiveTimeTest where
  toFun := positiveCoshTest G
  smooth := positiveCoshTest_smooth G hG δ hδ hz
  real := fun t => by unfold positiveCoshTest; split_ifs <;> simp [hr]
  left := δ
  right := R
  left_pos := hδ
  right_nonneg := hR
  support := positiveCoshTest_support G δ R hδ hR hz hs

theorem coshTestLift_positiveCoshTest (G : ℝ → ℂ) (q : ℝ) (hq : 1<q) :
    coshTestLift (positiveCoshTest G) q=G q := by
  simp only [coshTestLift,ite_eq_left hq,positiveCoshTest,ite_eq_left (Real.arcosh_pos hq),
    Real.cosh_arcosh hq.le]

/-- The positive-time test recovers the original geometric operator exactly;
no choice of smooth extension at or below q=1 is imposed. -/
theorem positiveTimeTestOfCosh_operator (N : ℕ) [NeZero N]
    (G : ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (hr : ∀ q,star (G q)=G q) (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (hz : ∀ q∈Icc 1 (Real.cosh δ),G q=0) (hs : Function.support G⊆Iic (Real.cosh R)) :
    positiveTimeAbelOperator N (positiveTimeTestOfCosh G hG hr δ R hδ hR hz hs)=
      abelKernelOperator N G hG hc R hR hs := by
  let ψ := positiveTimeTestOfCosh G hG hr δ R hδ hR hz hs
  exact abelKernelOperator_congr_above_one N ψ.lift G ψ.lift_smooth hG ψ.lift_compact hc
    R R hR hR ψ.lift_support hs (coshTestLift_positiveCoshTest G)

#print axioms positiveCoshTest_smooth
#print axioms positiveCoshTest_support
#print axioms positiveTimeTestOfCosh_operator

end QuantitativeMaass
