module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.Niven
public import Mathlib.Tactic

/-! Consolidated chapter: SmallLevelAnalyticRigidity. Original declarations and local scopes are retained. -/

/-! ## SmallLevelAnalyticRigidityV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelAnalyticRigidity

open Filter Set
open scoped Topology

/-- A nonzero analytic germ satisfying an automorphy identity at a fixed
point forces the multiplier to be a nonnegative integral power of the
derivative. This includes germs vanishing at the fixed point. -/
theorem multiplier_eq_derivative_pow {f φ u : ℂ → ℂ} {z₀ a : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hφ : HasDerivAt φ a z₀) (hfix : φ z₀ = z₀)
    (hu : ContinuousAt u z₀)
    (heq : ∀ᶠ z in 𝓝 z₀, f (φ z) = u z * f z)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ n : ℕ, u z₀ = a ^ n := by
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have ht : Tendsto φ (𝓝 z₀) (𝓝 z₀) := by
    simpa only [hfix] using hφ.continuousAt.tendsto
  have hs : Tendsto (fun z => (φ z - z₀) / (z - z₀)) (𝓝[≠] z₀) (𝓝 a) := by
    have hh := hφ.tendsto_slope
    change Tendsto (fun z => slope φ z₀ z) (𝓝[≠] z₀) (𝓝 a) at hh
    simpa only [slope_def_field, hfix] using hh
  have he : ∀ᶠ z in 𝓝[≠] z₀,
      ((φ z - z₀) / (z - z₀)) ^ n * g (φ z) = u z * g z := by
    filter_upwards [hfg.filter_mono nhdsWithin_le_nhds,
      (ht.eventually hfg).filter_mono nhdsWithin_le_nhds,
      heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hφz he hz0
    have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0
    simp only [smul_eq_mul] at hz hφz
    rw [hφz, hz] at he
    rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero n hzz)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using he
  have hl := (hs.pow n).mul ((hg.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds)
  have hr : Tendsto (fun z => u z * g z) (𝓝[≠] z₀) (𝓝 (u z₀ * g z₀)) :=
    (hu.mul hg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hh : a ^ n * g z₀ = u z₀ * g z₀ := tendsto_nhds_unique (hl.congr' he) hr
  exact ⟨n, (mul_right_cancel₀ hg0 hh).symm⟩

/-- If no order of vanishing is compatible with the fixed-point multiplier,
the analytic germ vanishes. -/
theorem eventually_zero_of_nonresonance {f φ u : ℂ → ℂ} {z₀ a : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hφ : HasDerivAt φ a z₀) (hfix : φ z₀ = z₀)
    (hu : ContinuousAt u z₀)
    (heq : ∀ᶠ z in 𝓝 z₀, f (φ z) = u z * f z)
    (hnon : ∀ n : ℕ, u z₀ ≠ a ^ n) : ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  by_contra hn
  obtain ⟨n, hn⟩ := multiplier_eq_derivative_pow hf hφ hfix hu heq hn
  exact hnon n hn

/-- Connected-domain version of the fixed-point rigidity argument. -/
theorem eqOn_zero_of_nonresonance {f φ u : ℂ → ℂ} {z₀ a : ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hz : z₀ ∈ U)
    (hφ : HasDerivAt φ a z₀) (hfix : φ z₀ = z₀) (hu : ContinuousAt u z₀)
    (heq : ∀ᶠ z in 𝓝 z₀, f (φ z) = u z * f z)
    (hnon : ∀ n : ℕ, u z₀ ≠ a ^ n) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz
    (eventually_zero_of_nonresonance (hf z₀ hz) hφ hfix hu heq hnon)

#print axioms multiplier_eq_derivative_pow
#print axioms eventually_zero_of_nonresonance
#print axioms eqOn_zero_of_nonresonance

end SmallLevelAnalyticRigidity
end
end

/-! ## SmallLevelMobiusRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelAnalyticRigidity

open Filter Set
open scoped Topology

theorem mobius_hasDerivAt {a b c d z : ℂ} (hdet : a*d-b*c=1) (hd : c*z+d ≠ 0) :
    HasDerivAt (fun w : ℂ => (a*w+b)/(c*w+d)) ((c*z+d)⁻¹ ^ 2) z := by
  have hh := (((hasDerivAt_id z).const_mul a).add_const b).div
    (((hasDerivAt_id z).const_mul c).add_const d) hd
  have hnum : a*(c*z+d)-(a*z+b)*c=1 := by
    calc
      _ = a*d-b*c := by ring
      _ = 1 := hdet
  convert hh using 1
  · rfl
  · simp only [mul_one, id_eq, hnum, one_div, inv_pow]

/-- Positive integral weight rules out every possible vanishing order for
a nontorsion elliptic multiplier. -/
theorem weight_nonresonance {v : ℂ} {k : ℕ} (hv : v ≠ 0) (hk : 0 < k)
    (hinf : ∀ j : ℕ, 0 < j → v ^ j ≠ 1) (n : ℕ) :
    v ^ k ≠ (v⁻¹ ^ 2) ^ n := by
  intro he
  have hp : v ^ (k + 2*n) = 1 := by
    rw [pow_add, he, pow_mul]
    simp only [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hv))
  exact hinf (k+2*n) (by omega) hp

/-- A holomorphic positive-weight function invariant under a determinant-one
Mobius map with an interior fixed point and nontorsion multiplier vanishes.
The derivative and order obstruction are proved rather than assumed. -/
theorem mobius_eqOn_zero {f : ℂ → ℂ} {U : Set ℂ} {a b c d z₀ : ℂ} {k : ℕ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hz : z₀ ∈ U)
    (hdet : a*d-b*c=1) (hd : c*z₀+d ≠ 0)
    (hfix : (a*z₀+b)/(c*z₀+d)=z₀) (hk : 0 < k)
    (hinf : ∀ j : ℕ, 0 < j → (c*z₀+d) ^ j ≠ 1)
    (heq : ∀ᶠ z in 𝓝 z₀, f ((a*z+b)/(c*z+d))=(c*z+d)^k*f z) :
    EqOn f 0 U := by
  apply eqOn_zero_of_nonresonance hf hU hz (mobius_hasDerivAt hdet hd) hfix
    (((continuousAt_id.const_mul c).add_const d).pow k) heq
  exact weight_nonresonance hd hk hinf

#print axioms mobius_hasDerivAt
#print axioms weight_nonresonance
#print axioms mobius_eqOn_zero

end SmallLevelAnalyticRigidity
end
end

/-! ## SmallLevelRationalTraceV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelAnalyticRigidity

open Filter Set
open scoped Topology

/-- A root of unity whose sum with its inverse is rational has integral
trace. This is the exact obstruction used for rational elliptic matrices. -/
theorem rational_trace_integral {v : ℂ} {t : ℚ} {j : ℕ} (hj : 0 < j)
    (hv : v ^ j = 1) (ht : v + v⁻¹ = (t : ℂ)) : ∃ m : ℤ, t = m := by
  have hvint : IsIntegral ℤ v := IsIntegral.of_pow hj (by rw [hv]; exact isIntegral_one)
  have hi : (v⁻¹) ^ j = 1 := by rw [inv_pow, hv, inv_one]
  have hiint : IsIntegral ℤ v⁻¹ := IsIntegral.of_pow hj (by rw [hi]; exact isIntegral_one)
  obtain ⟨m, hm⟩ := (hvint.add hiint).exists_int_iff_exists_rat.mp ⟨t, ht⟩
  refine ⟨m, ?_⟩
  have hh : (t : ℂ) = (m : ℂ) := ht.symm.trans hm
  exact_mod_cast hh

theorem fixed_point_trace {a b c d z : ℂ} (hdet : a*d-b*c=1)
    (hd : c*z+d ≠ 0) (hfix : (a*z+b)/(c*z+d)=z) :
    (c*z+d)+(c*z+d)⁻¹=a+d := by
  have he := (div_eq_iff hd).mp hfix
  have hp : (c*z+d)*(a+d-(c*z+d))=1 := by
    linear_combination hdet + c * he
  have hi : (c*z+d)⁻¹=a+d-(c*z+d) := by
    apply mul_left_cancel₀ hd
    rw [mul_inv_cancel₀ hd, hp]
  rw [hi]
  ring

/-- A rational nonintegral trace supplies the nontorsion condition from
matrix entries and an interior fixed point; no spectral premise is added. -/
theorem fixed_point_multiplier_nontorsion {a b c d z : ℂ} {t : ℚ}
    (hdet : a*d-b*c=1) (hd : c*z+d ≠ 0)
    (hfix : (a*z+b)/(c*z+d)=z) (htrace : a+d=(t : ℂ))
    (ht : ∀ m : ℤ, t ≠ m) : ∀ j : ℕ, 0 < j → (c*z+d)^j ≠ 1 := by
  intro j hj he
  obtain ⟨m, hm⟩ := rational_trace_integral hj he ((fixed_point_trace hdet hd hfix).trans htrace)
  exact ht m hm

/-- The rational-trace version of the elliptic defect-vanishing argument. -/
theorem rational_trace_eqOn_zero {f : ℂ → ℂ} {U : Set ℂ}
    {a b c d z₀ : ℂ} {t : ℚ} {k : ℕ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hz : z₀ ∈ U)
    (hdet : a*d-b*c=1) (hd : c*z₀+d ≠ 0)
    (hfix : (a*z₀+b)/(c*z₀+d)=z₀) (hk : 0 < k)
    (htrace : a+d=(t : ℂ)) (ht : ∀ m : ℤ, t ≠ m)
    (heq : ∀ᶠ z in 𝓝 z₀, f ((a*z+b)/(c*z+d))=(c*z+d)^k*f z) :
    EqOn f 0 U :=
  mobius_eqOn_zero hf hU hz hdet hd hfix hk
    (fixed_point_multiplier_nontorsion hdet hd hfix htrace ht) heq

#print axioms rational_trace_integral
#print axioms fixed_point_trace
#print axioms fixed_point_multiplier_nontorsion
#print axioms rational_trace_eqOn_zero

end SmallLevelAnalyticRigidity
end
end

/-! ## SmallLevelFractionalPeriodV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelAnalyticRigidity

open Complex Filter Set
open scoped Topology

/-- An explicit interior fixed point for S followed by a short translation. -/
theorem short_translation_fixed_point {t : ℝ} (ht : t^2 < 4) :
    ∃ z : ℂ, 0 < z.im ∧ z+(t : ℂ) ≠ 0 ∧ -1/(z+(t : ℂ))=z := by
  let s := Real.sqrt (4-t^2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s^2=4-t^2 := Real.sq_sqrt (by linarith)
  let z : ℂ := ⟨-t/2, s/2⟩
  have hz : 0 < z.im := by dsimp [z]; positivity
  have hd : z+(t : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at hh
    exact hz.ne' hh
  have hp : z*(z+(t : ℂ)) = -1 := by
    apply Complex.ext <;> simp [z, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs2]
  exact ⟨z, hz, hd, (div_eq_iff hd).mpr hp.symm⟩

/-- A positive-weight holomorphic function invariant under S and a rational
translation strictly between zero and one vanishes. This is the analytic
conclusion of the Fourier-filter lemma used at level 36, without assuming
cuspidality or excluding a constant Fourier term. -/
theorem fractional_period_eq_zero {f : ℂ → ℂ} {k : ℕ} {t : ℚ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im}) (hk : 0 < k)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hper : ∀ z : ℂ, 0 < z.im → f (z+(t : ℂ))=f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1/z)=z^k*f z) :
    ∀ z : ℂ, 0 < z.im → f z=0 := by
  have htR0 : (0 : ℝ) < t := by exact_mod_cast ht0
  have htR1 : (t : ℝ) < 1 := by exact_mod_cast ht1
  obtain ⟨z₀, hz₀, hd, hfix⟩ := short_translation_fixed_point (t := (t : ℝ))
    (by nlinarith)
  simp only [Complex.ofReal_ratCast] at hd hfix
  have hnon (m : ℤ) : t ≠ m := by
    intro hm
    have hlo : (0 : ℚ) < m := hm ▸ ht0
    have hhi : (m : ℚ) < 1 := hm ▸ ht1
    have hlo' : (0 : ℤ) < m := by exact_mod_cast hlo
    have hhi' : m < (1 : ℤ) := by exact_mod_cast hhi
    omega
  have heq : ∀ᶠ z in 𝓝 z₀,
      f ((0*z+(-1))/(1*z+(t : ℂ)))=(1*z+(t : ℂ))^k*f z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀] with z hz
    have hzt : 0 < (z+(t : ℂ)).im := by simpa using hz
    simpa only [zero_mul, zero_add, one_mul, hper z hz] using hS (z+(t : ℂ)) hzt
  have hall := rational_trace_eqOn_zero hf (convex_halfSpace_im_gt 0).isPreconnected hz₀
    (a := 0) (b := -1) (c := 1) (d := (t : ℂ)) (t := t)
    (by ring) (by simpa using hd) (by simpa using hfix) hk (by simp) hnon heq
  exact fun z hz => hall hz

#print axioms short_translation_fixed_point
#print axioms fractional_period_eq_zero

end SmallLevelAnalyticRigidity
end
end

/-! ## SmallLevelFiveFilterV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelAnalyticRigidity

/-- Exact cyclic elimination for the coefficients (0,-2,1,-1,1) in the
level-36 Hecke identity. The rational inverse is checked by ring arithmetic. -/
theorem five_cyclic_filter {x : ℕ → ℂ} {C : ℂ}
    (hp : Function.Periodic x 5)
    (he : ∀ n : ℕ, -2*x (n+1)+x (n+2)-x (n+3)+x (n+4)=C) : x 1=x 0 := by
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have h4 := he 4
  have h5 : x 5=x 0 := hp 0
  have h6 : x 6=x 1 := hp 1
  have h7 : x 7=x 2 := hp 2
  have h8 : x 8=x 3 := hp 3
  norm_num only [Nat.reduceAdd] at h0 h1 h2 h3 h4
  rw [h5] at h1 h2 h3 h4
  rw [h6] at h2 h3 h4
  rw [h7] at h3 h4
  rw [h8] at h4
  linear_combination (-12/41 : ℂ)*h0 + (-11/41 : ℂ)*h1 +
    (7/41 : ℂ)*h2 + (3/41 : ℂ)*h3 + (13/41 : ℂ)*h4

/-- The filter forces period one on a period-five function whenever its
output has period one. No Fourier expansion or growth assumption is needed. -/
theorem five_filter_period_one {g R : ℝ → ℂ}
    (hg : Function.Periodic g 5) (hR : Function.Periodic R 1)
    (he : ∀ t : ℝ, -2*g (t+6)+g (t+12)-g (t+18)+g (t+24)=R t) :
    Function.Periodic g 1 := by
  intro t
  let x : ℕ → ℂ := fun n => g (t+n)
  have hp : Function.Periodic x 5 := by
    intro n
    simpa only [x, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hg (t+n)
  have hred (s : ℝ) (j : ℕ) : g (s+6*j)=g (s+j) := by
    convert hg.nat_mul j (s+j) using 1
    congr 1
    ring
  have hx (n : ℕ) : -2*x (n+1)+x (n+2)-x (n+3)+x (n+4)=R t := by
    have hh := he (t+n)
    have h1 := hred (t+n) 1
    have h2 := hred (t+n) 2
    have h3 := hred (t+n) 3
    have h4 := hred (t+n) 4
    norm_num at h1 h2 h3 h4
    rw [h1, h2, h3, h4] at hh
    have hr : R (t+n)=R t := by simpa only [mul_one] using hR.nat_mul n t
    simpa only [x, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ← add_assoc, hr] using hh
  simpa only [x, Nat.cast_zero, Nat.cast_one, add_zero] using five_cyclic_filter hp hx

#print axioms five_cyclic_filter
#print axioms five_filter_period_one

end SmallLevelAnalyticRigidity
end
end

/-! ## SmallLevelHeckeFilterV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelAnalyticRigidity

open Complex

theorem upper_period_nat {f : ℂ → ℂ}
    (hp : ∀ z : ℂ, 0 < z.im → f (z+1)=f z)
    (z : ℂ) (hz : 0 < z.im) (n : ℕ) : f (z+n)=f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, ← add_assoc, hp (z+n) (by simpa using hz), ih]

/-- The concrete five-branch identity used in the level-36 proof forces
period 1/5. The two unspecified coefficients may be arbitrary complex
numbers, including zero. No cusp expansion is required for this step. -/
theorem hecke_filter_fifth_period {f : ℂ → ℂ} {A B : ℂ}
    (hp : ∀ z : ℂ, 0 < z.im → f (z+1)=f z)
    (he : ∀ z : ℂ, 0 < z.im →
      A*f (5*z)-2*f ((z+6)/5)+f ((z+12)/5)-f ((z+18)/5)+f ((z+24)/5)+B*f z=0) :
    ∀ z : ℂ, 0 < z.im → f (z+1/5)=f z := by
  intro z hz
  let g : ℝ → ℂ := fun x => f (z+(x : ℂ)/5)
  let R : ℝ → ℂ := fun x => -A*f (25*z+5*(x : ℂ))-B*f (5*z+(x : ℂ))
  have hg : Function.Periodic g 5 := by
    intro x
    dsimp [g]
    push_cast
    rw [show z+((x : ℂ)+5)/5=(z+(x : ℂ)/5)+1 by ring]
    apply hp
    simpa using hz
  have hR : Function.Periodic R 1 := by
    intro x
    dsimp [R]
    push_cast
    rw [show 25*z+5*((x : ℂ)+1)=(25*z+5*(x : ℂ))+5 by ring,
      show 5*z+((x : ℂ)+1)=(5*z+(x : ℂ))+1 by ring]
    have h5 : f ((25*z+5*(x : ℂ))+5)=f (25*z+5*(x : ℂ)) := by
      simpa only [Nat.cast_ofNat] using upper_period_nat hp (25*z+5*(x : ℂ))
        (by simpa using mul_pos (by norm_num : (0:ℝ)<25) hz) 5
    rw [h5, hp (5*z+(x : ℂ)) (by simpa using mul_pos (by norm_num : (0:ℝ)<5) hz)]
  have hrel (x : ℝ) : -2*g (x+6)+g (x+12)-g (x+18)+g (x+24)=R x := by
    have hh := he (5*z+(x : ℂ)) (by simpa using mul_pos (by norm_num : (0:ℝ)<5) hz)
    dsimp [g, R]
    push_cast
    ring_nf at hh ⊢
    linear_combination hh
  have hfin := five_filter_period_one hg hR hrel 0
  simpa [g] using hfin

/-- The full analytic Fourier-filter conclusion for the level-36
negative-sign obstruction, with all scalar coefficients unrestricted. -/
theorem hecke_filter_eq_zero {f : ℂ → ℂ} {k : ℕ} {A B : ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im}) (hk : 0 < k)
    (hp : ∀ z : ℂ, 0 < z.im → f (z+1)=f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1/z)=z^k*f z)
    (he : ∀ z : ℂ, 0 < z.im →
      A*f (5*z)-2*f ((z+6)/5)+f ((z+12)/5)-f ((z+18)/5)+f ((z+24)/5)+B*f z=0) :
    ∀ z : ℂ, 0 < z.im → f z=0 := by
  apply fractional_period_eq_zero hf hk (t := (1:ℚ)/5) (by norm_num) (by norm_num)
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hecke_filter_fifth_period hp he
  · exact hS

#print axioms upper_period_nat
#print axioms hecke_filter_fifth_period
#print axioms hecke_filter_eq_zero

end SmallLevelAnalyticRigidity
end
end
