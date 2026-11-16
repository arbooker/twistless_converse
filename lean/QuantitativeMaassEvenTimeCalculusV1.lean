module

public import QuantitativeMaassAbelIntegralV1
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Weighted averaging along a segment, used to remove division by time at zero. -/
def segmentAverage (k : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u in Icc (0:ℝ) 1,(u^k:ℝ) • f (u*x)

theorem segmentAverage_hasDerivAt (k : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (segmentAverage k f) (segmentAverage (k+1) (deriv f) x) x := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  obtain ⟨C,hC⟩ := hc.deriv.exists_bound_of_continuous hf'.continuous
  have hC0 : 0≤C := (norm_nonneg (deriv f 0)).trans (hC 0)
  have hcont (x : ℝ) : Continuous (fun u : ℝ => (u^k:ℝ) • f (u*x)) := by fun_prop
  have hd (u y : ℝ) : HasDerivAt (fun v => (u^k:ℝ) • f (u*v))
      ((u^(k+1):ℝ) • deriv f (u*y)) y := by
    have h := (((hf.differentiable (by simp)) (u*y)).hasDerivAt.scomp y
      ((hasDerivAt_id y).const_mul u)).fun_const_smul (u^k)
    simpa only [Function.comp_def,Pi.smul_apply,id_eq,mul_one,smul_smul,pow_succ] using h
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume.restrict (Icc (0:ℝ) 1))
    (F:=fun x u : ℝ => (u^k:ℝ) • f (u*x))
    (F':=fun x u : ℝ => (u^(k+1):ℝ) • deriv f (u*x))
    (bound:=fun _ => C) (s:=Set.univ) (univ_mem)
    (Eventually.of_forall (fun y => (hcont y).aestronglyMeasurable))
    ((hcont x).continuousOn.integrableOn_compact isCompact_Icc)
    (show AEStronglyMeasurable (fun u : ℝ => (u^(k+1):ℝ) • deriv f (u*x))
      (volume.restrict (Icc (0:ℝ) 1)) from (by fun_prop : Continuous _).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      intro y _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hu.1 _)]
      have hp : u^(k+1)≤1 := pow_le_one₀ hu.1 hu.2
      exact (mul_le_mul_of_nonneg_left (hC (u*y)) (pow_nonneg hu.1 _)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hC0))
    (integrable_const C) (Eventually.of_forall (fun u y _ => hd u y))
  exact h.2

theorem segmentAverage_deriv (k : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    deriv (segmentAverage k f)=segmentAverage (k+1) (deriv f) :=
  funext (fun x => (segmentAverage_hasDerivAt k f hf hc x).deriv)

theorem segmentAverage_smooth (k : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ContDiff ℝ ∞ (segmentAverage k f) := by
  have hn : ∀ n : ℕ,∀ k : ℕ,∀ f : ℝ → ℂ,ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ n (segmentAverage k f) := by
    intro n
    induction n with
    | zero =>
      intro k f hf hc
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (segmentAverage k f) from
        fun x => (segmentAverage_hasDerivAt k f hf hc x).differentiableAt).continuous
    | succ n ih =>
      intro k f hf hc
      rw [show (↑(n+1):ℕ∞ω)=(n:ℕ∞ω)+1 from by simp,contDiff_succ_iff_deriv]
      refine ⟨fun x => (segmentAverage_hasDerivAt k f hf hc x).differentiableAt,by simp,?_⟩
      rw [segmentAverage_deriv k f hf hc]
      exact ih (k+1) (deriv f) (contDiff_infty_iff_deriv.mp hf).2 hc.deriv
  exact contDiff_infty.mpr (fun n => hn n k f hf hc)

/-- The fundamental theorem gives an exact identity, including x=0. -/
theorem segmentAverage_deriv_identity (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    (x:ℝ) • segmentAverage 0 (deriv f) x=f x-f 0 := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hd (u : ℝ) : HasDerivAt (fun v => f (v*x)) (x • deriv f (u*x)) u := by
    simpa only [Function.comp_def,id_eq,one_mul] using
      (((hf.differentiable (by simp)) (u*x)).hasDerivAt.scomp u ((hasDerivAt_id u).mul_const x))
  have hi : IntervalIntegrable (fun u : ℝ => x • deriv f (u*x)) volume 0 1 :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ← integral_Icc_eq_integral_Ioc,integral_smul] at h
  simpa only [segmentAverage,pow_zero,one_smul,one_mul,zero_mul] using h

theorem even_time_deriv_odd (f : ℝ → ℂ) (he : Function.Even f) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have h := congrArg (fun g : ℝ → ℂ => deriv g x) (funext he)
  rw [deriv_comp_neg] at h
  exact neg_eq_iff_eq_neg.mp h

theorem even_time_deriv_zero (f : ℝ → ℂ) (he : Function.Even f) : deriv f 0=0 := by
  have h := even_time_deriv_odd f he 0
  simp only [neg_zero] at h
  have hz : deriv f 0+deriv f 0=0 := eq_neg_iff_add_eq_zero.mp h
  exact add_self_eq_zero.mp hz

theorem even_time_second_deriv_even (f : ℝ → ℂ) (he : Function.Even f) :
    Function.Even (deriv (deriv f)) := by
  intro x
  have h := congrArg (fun g : ℝ → ℂ => deriv g x) (funext (even_time_deriv_odd f he))
  rw [deriv_comp_neg,deriv.fun_neg] at h
  exact neg_injective h

/-- The nonsingular replacement of f'(x)/x for an even smooth profile. -/
def evenRadialDerivative (f : ℝ → ℂ) : ℝ → ℂ := segmentAverage 0 (deriv (deriv f))

theorem evenRadialDerivative_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (evenRadialDerivative f) :=
  segmentAverage_smooth 0 _ (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2
    hc.deriv.deriv

theorem evenRadialDerivative_identity (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (x : ℝ) : (x:ℝ) • evenRadialDerivative f x=deriv f x := by
  have h := segmentAverage_deriv_identity (deriv f) (contDiff_infty_iff_deriv.mp hf).2 x
  simpa only [evenRadialDerivative,even_time_deriv_zero f he,sub_zero] using h

theorem evenRadialDerivative_even (f : ℝ → ℂ) (he : Function.Even f) :
    Function.Even (evenRadialDerivative f) := by
  intro x
  unfold evenRadialDerivative segmentAverage
  simp only [mul_neg]
  apply integral_congr_ae
  filter_upwards with u
  rw [even_time_second_deriv_even f he (u*x)]

theorem evenRadialDerivative_zero (f : ℝ → ℂ) :
    evenRadialDerivative f 0=deriv (deriv f) 0 := by
  simp [evenRadialDerivative,segmentAverage,Real.volume_real_Icc_of_le (by norm_num : (0:ℝ)≤1)]

theorem evenRadialDerivative_compact (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) : HasCompactSupport (evenRadialDerivative f) := by
  obtain ⟨B,hB,hbound⟩ := hc.deriv.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  apply (isCompact_Icc : IsCompact (Icc (-B) B)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_cases hz : x=0
  · subst x
    exact ⟨by linarith, hB.le⟩
  · have hd : deriv f x≠0 := by
      rw [← evenRadialDerivative_identity f hf he x]
      exact smul_ne_zero hz hx
    have h := hbound (subset_tsupport _ hd)
    apply abs_le.mp
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using h

/-- Descent through the square map, defined on the nonnegative half-line. -/
def evenSquareLift (f : ℝ → ℂ) (q : ℝ) : ℂ := f (Real.sqrt q)

theorem evenSquareLift_hasDerivAt_pos (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (q : ℝ) (hq : 0<q) :
    HasDerivAt (evenSquareLift f) ((1/2:ℝ) • evenSquareLift (evenRadialDerivative f) q) q := by
  have h := (((hf.differentiable (by simp)) (Real.sqrt q)).hasDerivAt.scomp q
    (Real.hasDerivAt_sqrt hq.ne'))
  have hn : Real.sqrt q≠0 := (Real.sqrt_pos.mpr hq).ne'
  have hid : (1/(2*Real.sqrt q):ℝ) • deriv f (Real.sqrt q)=
      (1/2:ℝ) • evenRadialDerivative f (Real.sqrt q) := by
    rw [← evenRadialDerivative_identity f hf he (Real.sqrt q),smul_smul]
    congr 1
    field_simp
  change HasDerivAt (fun x => f (Real.sqrt x)) ((1/2:ℝ) • evenRadialDerivative f (Real.sqrt q)) q
  simpa only [Function.comp_def,hid] using h

/-- The derivative at the boundary follows from its continuous one-sided
limit; no differentiability of sqrt at zero is asserted. -/
theorem evenSquareLift_hasDerivWithinAt (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) (q : ℝ) (hq : 0≤q) :
    HasDerivWithinAt (evenSquareLift f)
      ((1/2:ℝ) • evenSquareLift (evenRadialDerivative f) q) (Ici 0) q := by
  by_cases hz : q=0
  · subst q
    have hg : Continuous (fun x => (1/2:ℝ) • evenSquareLift (evenRadialDerivative f) x) := by
      have hd := (evenRadialDerivative_smooth f hf hc).continuous
      unfold evenSquareLift
      fun_prop
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s:=Ioi (0:ℝ))
    · intro x hx
      exact (evenSquareLift_hasDerivAt_pos f hf he x hx).differentiableAt.differentiableWithinAt
    · exact (hf.continuous.comp Real.continuous_sqrt).continuousAt.continuousWithinAt
    · exact self_mem_nhdsWithin
    · apply ((hg.tendsto 0).mono_left inf_le_left).congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (evenSquareLift_hasDerivAt_pos f hf he x hx).deriv.symm
  · exact (evenSquareLift_hasDerivAt_pos f hf he q (lt_of_le_of_ne hq (Ne.symm hz))).hasDerivWithinAt

/-- Every even compact smooth time profile descends smoothly through x^2,
including the boundary. This supplies all orders, not just a continuous lift. -/
theorem evenSquareLift_smoothOn (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ ∞ (evenSquareLift f) (Ici 0) := by
  have hn : ∀ n : ℕ,∀ f : ℝ → ℂ,ContDiff ℝ ∞ f → Function.Even f → HasCompactSupport f →
      ContDiffOn ℝ n (evenSquareLift f) (Ici 0) := by
    intro n
    induction n with
    | zero =>
      intro f hf he hc
      exact contDiffOn_zero.mpr (hf.continuous.comp Real.continuous_sqrt).continuousOn
    | succ n ih =>
      intro f hf he hc
      rw [show (↑(n+1):ℕ∞ω)=(n:ℕ∞ω)+1 from by simp,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici (0:ℝ))]
      refine ⟨fun x hx => (evenSquareLift_hasDerivWithinAt f hf he hc x hx).differentiableWithinAt,
        by simp,?_⟩
      have hd := (ih (evenRadialDerivative f) (evenRadialDerivative_smooth f hf hc)
        (evenRadialDerivative_even f he) (evenRadialDerivative_compact f hf he hc)).const_smul (1/2:ℝ)
      apply hd.congr
      intro x hx
      exact (evenSquareLift_hasDerivWithinAt f hf he hc x hx).derivWithin
        (uniqueDiffOn_Ici (0:ℝ) x hx)
  exact contDiffOn_infty.mpr (fun n => hn n f hf he hc)

/-- A radial lift whose regularity at q=1 is proved through the square-map
lemma and the globally smooth odd arsinh coordinate. -/
def evenCoshLift (f : ℝ → ℂ) (q : ℝ) : ℂ :=
  f (2*Real.arsinh (Real.sqrt ((q-1)/2)))

theorem evenCoshLift_argument (q : ℝ) (hq : 1≤q) :
    2*Real.arsinh (Real.sqrt ((q-1)/2))=Real.arcosh q := by
  apply Real.cosh_injOn
  · exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _))
  · exact Real.arcosh_nonneg hq
  · rw [Real.cosh_two_mul,Real.cosh_sq,Real.sinh_arsinh,
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hq) (by norm_num)),Real.cosh_arcosh hq]
    ring

theorem evenCoshLift_smoothOn (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (hc : HasCompactSupport f) :
    ContDiffOn ℝ ∞ (evenCoshLift f) (Ici 1) := by
  let g : ℝ → ℂ := fun x => f (2*Real.arsinh x)
  have hg : ContDiff ℝ ∞ g := by dsimp [g]; fun_prop
  have hge : Function.Even g := by
    intro x
    dsimp [g]
    rw [Real.arsinh_neg,mul_neg,he]
  have hgc : HasCompactSupport g := by
    have h := (hc.comp_homeomorph (Homeomorph.mulLeft₀ (2:ℝ) (by norm_num))).comp_homeomorph
      Real.sinhHomeomorph.symm
    exact h
  have hs := evenSquareLift_smoothOn g hg hge hgc
  exact hs.comp (show ContDiffOn ℝ ∞ (fun q : ℝ => (q-1)/2) (Ici 1) by fun_prop)
    (fun q hq => div_nonneg (sub_nonneg.mpr hq) (by norm_num))

/-- Exact recovery of the original even time test, including time zero. -/
theorem evenCoshLift_time (f : ℝ → ℂ) (he : Function.Even f) (t : ℝ) :
    evenCoshLift f (Real.cosh t)=f t := by
  unfold evenCoshLift
  rw [evenCoshLift_argument _ (Real.one_le_cosh t)]
  have ha : Real.arcosh (Real.cosh t)=|t| := by
    rw [← Real.cosh_abs t]
    exact Real.arcosh_cosh (abs_nonneg t)
  rw [ha]
  by_cases ht : 0≤t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht),he]

theorem evenCoshLift_real (f : ℝ → ℂ) (hr : ∀ t,star (f t)=f t) (q : ℝ) :
    star (evenCoshLift f q)=evenCoshLift f q := hr _

/-- Compact time support bounds the radial lift on its physical domain q>=1. -/
theorem evenCoshLift_zero_above (f : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (q : ℝ) (hq : Real.cosh R<q) :
    evenCoshLift f q=0 := by
  have hq1 : 1≤q := (Real.one_le_cosh R).trans hq.le
  unfold evenCoshLift
  rw [evenCoshLift_argument q hq1]
  by_contra hn
  have ht := (hs hn).2
  have h := Real.cosh_le_cosh.mpr (show |Real.arcosh q|≤|R| from by
    rw [abs_of_nonneg (Real.arcosh_nonneg hq1),abs_of_nonneg hR]
    exact ht)
  rw [Real.cosh_arcosh hq1] at h
  exact (not_le_of_gt hq) h

#print axioms evenCoshLift_argument
#print axioms evenCoshLift_smoothOn
#print axioms evenCoshLift_time
#print axioms evenCoshLift_real
#print axioms evenCoshLift_zero_above

#print axioms evenSquareLift_hasDerivAt_pos
#print axioms evenSquareLift_hasDerivWithinAt
#print axioms evenSquareLift_smoothOn

#print axioms segmentAverage_hasDerivAt
#print axioms segmentAverage_deriv
#print axioms segmentAverage_smooth
#print axioms segmentAverage_deriv_identity
#print axioms even_time_deriv_odd
#print axioms even_time_deriv_zero
#print axioms even_time_second_deriv_even
#print axioms evenRadialDerivative_smooth
#print axioms evenRadialDerivative_identity
#print axioms evenRadialDerivative_even
#print axioms evenRadialDerivative_zero
#print axioms evenRadialDerivative_compact

end QuantitativeMaass
