module
public import SmallLevelTwentySixPariFirstChartTheoryV4
public import SmallLevelTwentySixPhysicalModulusTheoryV4
public import SmallLevelTwentySixRootTheoryV4
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariLinearFactorExclusion
open SmallLevelTwentySixPariFirstChart SmallLevelTwentySixPhysicalModulus

theorem low_curve_one (y z w a b u : ℂ) :
    lowCurve 1 y z w a b u=(208/225:ℂ)*(y^2-3*y-19) := by
  norm_num [lowCurve,SmallLevelTwentySixPariIdentity007.p1] <;> ring

theorem low_curve_neg_five (y z w a b u : ℂ) :
    lowCurve (-5) y z w a b u=(8/225:ℂ)*
      (9828*y^3-294684*y^2+2884115*y-9120293) := by
  norm_num [lowCurve,SmallLevelTwentySixPariIdentity007.p1] <;> ring

theorem unit_disk_impossible (y : ℂ) (hy : ‖y‖≤1)
    (hp : y^2-3*y-19=0) : False := by
  have he : y^2-3*y=19 := by linear_combination hp
  have hb:=norm_sub_le (y^2) (3*y)
  rw [he] at hb
  norm_num [norm_pow,norm_mul] at hb
  have hs : ‖y‖^2≤1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (norm_nonneg y)]
  nlinarith

theorem outside_large_disk_impossible (y : ℂ) (hy : 125≤‖y‖)
    (hp : 9828*y^3-294684*y^2+2884115*y-9120293=0) : False := by
  have he : 9828*y^3=(294684*y^2-2884115*y)+9120293 := by linear_combination hp
  have hb : 9828*‖y‖^3≤294684*‖y‖^2+2884115*‖y‖+9120293 := by
    calc
      9828*‖y‖^3=‖(9828:ℂ)*y^3‖ := by norm_num [norm_mul,norm_pow]
      _=‖(294684*y^2-2884115*y)+9120293‖ := congrArg norm he
      _≤‖294684*y^2-2884115*y‖+‖(9120293:ℂ)‖ := norm_add_le _ _
      _≤(‖(294684:ℂ)*y^2‖+‖(2884115:ℂ)*y‖)+‖(9120293:ℂ)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _=294684*‖y‖^2+2884115*‖y‖+9120293 := by norm_num [norm_mul,norm_pow]
  have h2:=mul_nonneg (sub_nonneg.mpr hy) (norm_nonneg y)
  have h3:=mul_nonneg (sub_nonneg.mpr hy) (sq_nonneg ‖y‖)
  nlinarith

/-- The x=1 factor is excluded using only the physical modulus bounds and
 the low-degree curve, without further large syzygy certificates. -/
theorem no_physical_one (h z w a b u : ℂ)
    (hx : ‖(2:ℂ)^h‖^2=1) (hp : lowCurve 1 ((9:ℂ)^h) z w a b u=0) : False := by
  rw [low_curve_one] at hp
  have he:=(mul_eq_zero.mp hp).resolve_left (by norm_num : (208/225:ℂ)≠0)
  have hy : ‖(9:ℂ)^h‖≤1 := by
    rcases physical_bounds h with hh|hh <;> rw [hx] at hh <;> norm_num at hh
    · nlinarith [norm_nonneg ((9:ℂ)^h)]
    · nlinarith [norm_nonneg ((9:ℂ)^h)]
  exact unit_disk_impossible _ hy he

/-- The x=-5 factor is excluded by the same physical bounds. -/
theorem no_physical_neg_five (h z w a b u : ℂ)
    (hx : ‖(2:ℂ)^h‖^2=25) (hp : lowCurve (-5) ((9:ℂ)^h) z w a b u=0) : False := by
  rw [low_curve_neg_five] at hp
  have he:=(mul_eq_zero.mp hp).resolve_left (by norm_num : (8/225:ℂ)≠0)
  have hs : 15625≤‖(9:ℂ)^h‖^2 := by
    rcases physical_bounds h with hh|hh <;> rw [hx] at hh <;> norm_num at hh
    exact hh.1
  have hy : 125≤‖(9:ℂ)^h‖ := by
    by_contra hn
    have hn' : 0<125-‖(9:ℂ)^h‖ := by linarith
    have hh:=mul_pos hn' (show 0<125+‖(9:ℂ)^h‖ by positivity)
    nlinarith
  exact outside_large_disk_impossible _ hy he

#print axioms low_curve_one
#print axioms low_curve_neg_five
#print axioms no_physical_one
#print axioms no_physical_neg_five

/-- Apply the two linear-factor exclusions to the actual signed prime parameters. -/
theorem no_signed_linear_parameters (m : ℕ) (s u z w a b θ : ℂ)
    (hu : u=1 ∨ u= -1)
    (hx : u*SmallLevelPrimeRates.parameter 2 m s=1 ∨
      u*SmallLevelPrimeRates.parameter 2 m s= -5)
    (hp : lowCurve (u*SmallLevelPrimeRates.parameter 2 m s)
      ((SmallLevelPrimeRates.parameter 3 m s)^2) z w a b θ=0) : False := by
  have hun : ‖u‖=1 := by rcases hu with rfl|rfl <;> norm_num
  rw [SmallLevelTwentySixRoot.parameter_three_squared] at hp
  rcases hx with hx|hx
  · rw [hx] at hp
    have hn:=congrArg (fun v : ℂ => ‖v‖^2) hx
    have hc : ‖(1:ℂ)‖^2=(1:ℝ) := by norm_num
    rw [norm_mul,hun,one_mul,hc] at hn
    exact no_physical_one (s-(m:ℂ)) z w a b θ (by simpa only [SmallLevelPrimeRates.parameter,Nat.cast_ofNat] using hn) hp
  · rw [hx] at hp
    have hn:=congrArg (fun v : ℂ => ‖v‖^2) hx
    have hc : ‖(-5:ℂ)‖^2=(25:ℝ) := by norm_num
    rw [norm_mul,hun,one_mul,hc] at hn
    exact no_physical_neg_five (s-(m:ℂ)) z w a b θ (by simpa only [SmallLevelPrimeRates.parameter,Nat.cast_ofNat] using hn) hp

#print axioms no_signed_linear_parameters
end SmallLevelTwentySixPariLinearFactorExclusion
