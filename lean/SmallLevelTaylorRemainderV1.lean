module

public import SmallLevelTaylorFamilyBoundV1
public import SmallLevelCauchyRemainderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set Metric FinitenessPolynomialSeries
open scoped Topology

def taylorRemainder (k : ℕ) (a : ℕ → ℂ) (β c r : ℝ) (M : ℕ) (y : ℝ) : ℂ :=
  deformed k a β c y (((y/r:ℝ):ℂ)*I)-
    (cauchyPowerSeries (deformed k a β c y) 0 (1/2)).partialSum M (((y/r:ℝ):ℂ)*I)

theorem deformation_parameter_norm {r y : ℝ} (hy : 0≤y) :
    ‖((y/r:ℝ):ℂ)*I‖=y/|r| := by
  rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_nonneg hy]

theorem taylorRemainder_bound (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (K : ℕ) {D : ℝ} (hD : 0≤D) {β c r y : ℝ} (hc : 0<c) (hr : r≠0)
    (hy : 0<y) (hsmall : y≤|r|/4)
    (hbound : ∀ u : ℂ, ‖u‖≤1/2 → ‖deformed k a β c y u‖≤D/y^K) (M : ℕ) :
    ‖taylorRemainder k a β c r M y‖≤
      (2*D*(2/|r|)^M)*y^((M:ℝ)-(K:ℝ)) := by
  have hrpos : 0 < |r| := abs_pos.mpr hr
  have hu : ‖((y/r:ℝ):ℂ)*I‖≤1/4 := by
    rw [deformation_parameter_norm hy.le]
    exact (div_le_iff₀ hrpos).mpr (by linarith)
  have hdiff : DifferentiableOn ℂ (deformed k a β c y) (closedBall 0 (1/2)) := by
    intro u hu
    apply (deformed_analytic k ha β hc hy _).differentiableAt.differentiableWithinAt
    simpa only [mem_closedBall,dist_zero_right] using hu
  have h := cauchy_remainder_bound hdiff (D := D/y^K) (by positivity) hbound hu M
  change ‖taylorRemainder k a β c r M y‖≤_ at h
  rw [deformation_parameter_norm hy.le] at h
  calc
    _≤2*(D/y^K)*(2*(y/|r|))^M := h
    _=(2*D*(2/|r|)^M)*y^((M:ℝ)-(K:ℝ)) := by
      rw [Real.rpow_sub hy,Real.rpow_natCast,Real.rpow_natCast]
      simp only [mul_pow,div_eq_mul_inv]
      ring

/-- The actual deformed Fourier family has a movable Taylor remainder.
The single exponent K is chosen before beta, the translation r and the order
M. In particular it does not grow with the number of retained Taylor terms. -/
theorem taylorRemainder_small {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (k : ℕ) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β r : ℝ, r≠0 → ∀ M : ℕ,
      taylorRemainder k a β c r M=O[𝓝[>] 0]
        (fun y : ℝ => y^((M:ℝ)-(K:ℝ))) := by
  obtain ⟨K,D,hD,hbound⟩ := deformed_family_bound k ha ha0 hc
  refine ⟨K,fun β r hr M => IsBigO.of_bound (2*D*(2/|r|)^M) ?_⟩
  have hsmall : ∀ᶠ y : ℝ in 𝓝[>] 0, y≤|r|/4 := by
    have hrpos : 0 < |r| := abs_pos.mpr hr
    exact ((eventually_lt_nhds (by positivity : (0:ℝ) < |r|/4)).mono
      (fun _ h => h.le)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall] with y hy hys
  change 0<y at hy
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy.le _)]
  exact taylorRemainder_bound k ha K hD hc hr hy hys (hbound β y hy) M

theorem original_taylorRemainder_small {N k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {c : ℝ} (hc : 0<c) :
    ∃ K : ℕ, ∀ β r : ℝ, r≠0 → ∀ M : ℕ,
      taylorRemainder k (FinitenessOriginalFourier.fullCoefficients f k) β c r M
        =O[𝓝[>] 0] (fun y : ℝ => y^((M:ℝ)-(K:ℝ))) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  exact taylorRemainder_small (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero k) k hc

#print axioms deformation_parameter_norm
#print axioms taylorRemainder_bound
#print axioms taylorRemainder_small
#print axioms original_taylorRemainder_small

end SmallLevelTaylor
