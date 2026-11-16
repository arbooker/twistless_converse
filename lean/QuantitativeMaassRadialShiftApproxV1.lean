module

public import QuantitativeMaassEvenTimeCalculusV1
public import QuantitativeMaassAbelCutoffV1
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A smooth lower cutoff, already constant one below the physical boundary. -/
def radialShiftCutoff (a q : ℝ) : ℂ := Real.smoothTransition (4*(q-1)/a+2)

def radialShiftApprox (F : ℝ → ℂ) (a q : ℝ) : ℂ := radialShiftCutoff a q*F (q+a)

theorem radialShiftCutoff_smooth (a : ℝ) : ContDiff ℝ ∞ (radialShiftCutoff a) := by
  exact Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞
    (fun q : ℝ => Real.smoothTransition (4*(q-1)/a+2)) by fun_prop)

theorem radialShiftCutoff_zero (a q : ℝ) (ha : 0<a) (hq : q≤1-a/2) :
    radialShiftCutoff a q=0 := by
  have h : 4*(q-1)/a+2≤0 := by
    have hh : 4*(q-1)/a≤ -2 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp only [radialShiftCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero]

theorem radialShiftCutoff_one (a q : ℝ) (ha : 0<a) (hq : 1-a/4≤q) :
    radialShiftCutoff a q=1 := by
  have h : 1≤4*(q-1)/a+2 := by
    have hh : -1≤4*(q-1)/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  simp only [radialShiftCutoff,Real.smoothTransition.one_of_one_le h,Complex.ofReal_one]

theorem radialShiftApprox_zero_below (F : ℝ → ℂ) (a q : ℝ) (ha : 0<a)
    (hq : q≤1-a/2) : radialShiftApprox F a q=0 := by
  simp only [radialShiftApprox,radialShiftCutoff_zero a q ha hq,zero_mul]

theorem radialShiftApprox_eq_shift (F : ℝ → ℂ) (a q : ℝ) (ha : 0<a)
    (hq : 1-a/4≤q) : radialShiftApprox F a q=F (q+a) := by
  simp only [radialShiftApprox,radialShiftCutoff_one a q ha hq,one_mul]

/-- Global smoothness is obtained using only smoothness on q>=1. The
cutoff vanishes on a neighborhood of every point outside the shifted domain. -/
theorem radialShiftApprox_smooth (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (a : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (radialShiftApprox F a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 1-a<q
  · have hqa : 1<q+a := by linarith
    have hlocal := (hF (q+a) hqa.le).contDiffAt (Ici_mem_nhds hqa)
    exact (radialShiftCutoff_smooth a).contDiffAt.mul
      (hlocal.comp q (contDiffAt_id.add contDiffAt_const))
  · have hq' : q<1-a/2 := by linarith
    have hz : radialShiftApprox F a=ᶠ[𝓝 q] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hq'] with x hx
      exact radialShiftApprox_zero_below F a x ha hx.le
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem radialShiftApprox_support (F : ℝ → ℂ) (B : ℝ)
    (hB : ∀ q,B<q → F q=0) (a : ℝ) (ha : 0<a) :
    Function.support (radialShiftApprox F a)⊆Icc (1-a/2) (B-a) := by
  intro q hq
  constructor
  · by_contra hn
    exact hq (radialShiftApprox_zero_below F a q ha (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    have hz : F (q+a)=0 := hB _ (by linarith [lt_of_not_ge hn])
    exact hq (by simp only [radialShiftApprox,hz,mul_zero])

theorem radialShiftApprox_compact (F : ℝ → ℂ) (B : ℝ)
    (hB : ∀ q,B<q → F q=0) (a : ℝ) (ha : 0<a) :
    HasCompactSupport (radialShiftApprox F a) :=
  (isCompact_Icc : IsCompact (Icc (1-a/2) (B-a))).of_isClosed_subset isClosed_closure
    (closure_minimal (radialShiftApprox_support F B hB a ha) isClosed_Icc)

theorem radialShiftApprox_upper_support (F : ℝ → ℂ) (B : ℝ)
    (hB : ∀ q,B<q → F q=0) (a : ℝ) (ha : 0<a) :
    Function.support (radialShiftApprox F a)⊆Iic B := by
  intro q hq
  have h := (radialShiftApprox_support F B hB a ha hq).2
  change q≤B
  linarith

theorem radialShiftApprox_real (F : ℝ → ℂ) (hF : ∀ q,star (F q)=F q)
    (a q : ℝ) : star (radialShiftApprox F a q)=radialShiftApprox F a q := by
  simp only [radialShiftApprox,radialShiftCutoff,map_mul,Complex.star_def,Complex.conj_ofReal]
  rw [← Complex.star_def,hF]

/-- Every derivative on the physical domain is exactly the shifted
one-sided derivative of the source. -/
theorem radialShiftApprox_iteratedDeriv (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 1≤q) (k : ℕ) :
    iteratedDeriv k (radialShiftApprox F a) q=iteratedDerivWithin k F (Ici 1) (q+a) := by
  have he : radialShiftApprox F a=ᶠ[𝓝 q] (fun x => F (x+a)) := by
    filter_upwards [Ioi_mem_nhds (show 1-a/4<q by linarith)] with x hx
    exact radialShiftApprox_eq_shift F a x ha hx.le
  rw [he.iteratedDeriv_eq,iteratedDeriv_comp_add_const]
  symm
  apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (1:ℝ))
  · exact ((hF (q+a) (by change 1≤q+a; linarith)).contDiffAt
      (Ici_mem_nhds (by linarith : 1<q+a))).of_le (by simp)
  · change 1≤q+a
    linarith

/-- All radial derivatives converge pointwise, including at q=1. -/
theorem radialShiftApprox_derivatives_tendsto {ι : Type*} (l : Filter ι)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) (q : ℝ) (hq : 1≤q) (k : ℕ) :
    Tendsto (fun i => iteratedDeriv k (radialShiftApprox F (a i)) q) l
      (𝓝 (iteratedDerivWithin k F (Ici 1) q)) := by
  have hshift : Tendsto (fun i => q+a i) l (𝓝[Ici 1] q) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall (fun i => ?_)⟩
    · simpa only [add_zero] using ha0.const_add q
    · change 1≤q+a i
      have hi := ha i
      linarith
  have h := ((hF.continuousOn_iteratedDerivWithin (m:=k) (by simp)
    (uniqueDiffOn_Ici (1:ℝ))) q hq).tendsto.comp hshift
  apply h.congr'
  filter_upwards with i
  exact (radialShiftApprox_iteratedDeriv F hF (a i) (ha i) q hq k).symm

/-- The time profiles of the approximants converge to the original even
time test, rather than to an assumed abstract radial transform. -/
theorem radialShiftApprox_cosh_tendsto {ι : Type*} (l : Filter ι)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (hc : HasCompactSupport f)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) (t : ℝ) :
    Tendsto (fun i => radialShiftApprox (evenCoshLift f) (a i) (Real.cosh t)) l (𝓝 (f t)) := by
  have h := radialShiftApprox_derivatives_tendsto l (evenCoshLift f)
    (evenCoshLift_smoothOn f hf he hc) a ha ha0 (Real.cosh t) (Real.one_le_cosh t) 0
  simpa only [iteratedDeriv_zero,iteratedDerivWithin_zero,evenCoshLift_time f he] using h

#print axioms radialShiftCutoff_smooth
#print axioms radialShiftCutoff_zero
#print axioms radialShiftCutoff_one
#print axioms radialShiftApprox_zero_below
#print axioms radialShiftApprox_eq_shift
#print axioms radialShiftApprox_smooth
#print axioms radialShiftApprox_support
#print axioms radialShiftApprox_compact
#print axioms radialShiftApprox_upper_support
#print axioms radialShiftApprox_real
#print axioms radialShiftApprox_iteratedDeriv
#print axioms radialShiftApprox_derivatives_tendsto
#print axioms radialShiftApprox_cosh_tendsto

end QuantitativeMaass
