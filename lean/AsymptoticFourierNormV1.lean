module

public import AsymptoticGammaTailV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFourierNorm

open MeasureTheory Set Filter AsymptoticGammaTail
open scoped Topology

/-- The radial density of a periodic holomorphic Fourier mode in the
capped weighted cylinder. Here m=k-2 and r=4πn. Integer t suffices for
choosing the fixed reconstruction weight. -/
noncomputable def density (m t : ℕ) (r ε y : ℝ) : ℝ :=
  kernel m r y*(min (y/ε) 1)^(2*t)

noncomputable def beta (m t : ℕ) (r ε : ℝ) : ℝ :=
  ∫ y in Ioi 0,density m t r ε y

theorem density_nonneg (m t : ℕ) (r : ℝ) {ε y : ℝ} (hε : 0<ε) (hy : 0≤y) :
    0≤density m t r ε y := by
  dsimp [density,kernel]
  positivity

theorem uncapped_identity (m t : ℕ) (r ε y : ℝ) :
    kernel m r y*(y/ε)^(2*t)=(1/ε)^(2*t)*kernel (m+2*t) r y := by
  simp only [kernel,pow_add,div_pow,one_div]
  ring

theorem density_le_uncapped (m t : ℕ) (r : ℝ) {ε y : ℝ} (hε : 0<ε) (hy : 0≤y) :
    density m t r ε y≤(1/ε)^(2*t)*kernel (m+2*t) r y := by
  rw [← uncapped_identity]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_min (div_nonneg hy hε.le) zero_le_one) (min_le_left _ _) _)
    (kernel_nonneg m r hy)

theorem density_eq_uncapped (m t : ℕ) (r : ℝ) {ε y : ℝ} (hε : 0<ε) (hy : y≤ε) :
    density m t r ε y=(1/ε)^(2*t)*kernel (m+2*t) r y := by
  rw [density,min_eq_left ((div_le_one hε).mpr hy)]
  exact uncapped_identity m t r ε y

theorem integrable_density (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    Integrable (density m t r ε) (volume.restrict (Ioi 0)) := by
  apply ((integrable_kernel (m+2*t) hr).const_mul ((1/ε)^(2*t))).mono_nonneg
  · have h : Continuous (density m t r ε) := by unfold density kernel; fun_prop
    exact h.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact density_nonneg m t r hε hy.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact density_le_uncapped m t r hε hy.le

theorem beta_nonneg (m t : ℕ) {r ε : ℝ} (hε : 0<ε) : 0≤beta m t r ε := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact density_nonneg m t r hε hy.le

theorem beta_pos (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) : 0<beta m t r ε := by
  have hp : ∀ y∈Ioi (0:ℝ),0<density m t r ε y := by
    intro y hy
    dsimp [density,kernel]
    have : 0<y := hy
    positivity
  have hs : Function.support (density m t r ε) ∩ Ioi 0=Ioi 0 := by
    rw [inter_eq_right]
    intro y hy
    exact (hp y hy).ne'
  unfold beta
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs,Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hp y hy).le
  · exact integrable_density m t hr hε

theorem beta_le_uncapped (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    beta m t r ε≤(1/ε)^(2*t)*(1/r)^(m+2*t+1)*((m+2*t).factorial:ℝ) := by
  calc
    beta m t r ε ≤ ∫ y in Ioi 0,(1/ε)^(2*t)*kernel (m+2*t) r y := by
      apply integral_mono_ae (integrable_density m t hr hε)
        ((integrable_kernel (m+2*t) hr).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact density_le_uncapped m t r hε hy.le
    _ = _ := by rw [integral_const_mul,integral_kernel _ hr]; ring

/-- Markov's half-mass estimate supplies the needed lower bound for the
actual capped Fourier norm, uniformly once the frequency is large enough. -/
theorem half_uncapped_le_beta (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε)
    (hthreshold : 2*((m+2*t:ℕ)+1:ℝ)≤r*ε) :
    (1/ε)^(2*t)*((1/r)^(m+2*t+1)*((m+2*t).factorial:ℝ))/2≤beta m t r ε := by
  have hd := integrable_density m t hr hε
  have hd0 : 0≤ᵐ[volume.restrict (Ioi 0)] density m t r ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact density_nonneg m t r hε hy.le
  calc
    _ ≤ (1/ε)^(2*t)*(∫ y in Iic ε,kernel (m+2*t) r y ∂(volume.restrict (Ioi 0))) := by
      have h := mul_le_mul_of_nonneg_left (half_kernel_below (m+2*t) hr hε hthreshold)
        (by positivity : 0≤(1/ε)^(2*t))
      nlinarith
    _ = ∫ y in Iic ε,density m t r ε y ∂(volume.restrict (Ioi 0)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Iic
      intro y hy
      exact (density_eq_uncapped m t r hε hy).symm
    _ ≤ _ := setIntegral_le_integral hd hd0

theorem density_succ_le (m t : ℕ) (r : ℝ) {ε y : ℝ} (hε : 0<ε) (hy : 0≤y) :
    density m (t+1) r ε y≤density m t r ε y := by
  have hb0 : 0≤min (y/ε) 1 := le_min (div_nonneg hy hε.le) zero_le_one
  have hb1 : min (y/ε) 1≤1 := min_le_right _ _
  have hb2 : (min (y/ε) 1)^2≤1 := by nlinarith
  have he : density m (t+1) r ε y=density m t r ε y*(min (y/ε) 1)^2 := by
    simp only [density,Nat.mul_add,Nat.mul_one,pow_add]
    ring
  rw [he]
  exact mul_le_of_le_one_right (density_nonneg m t r hε hy) hb2

theorem beta_succ_le (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    beta m (t+1) r ε≤beta m t r ε := by
  apply integral_mono_ae (integrable_density m (t+1) hr hε) (integrable_density m t hr hε)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact density_succ_le m t r hε hy.le

theorem ratio_le_one (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε) :
    beta m (t+1) r ε / beta m t r ε ≤ 1 := by
  by_cases hz : beta m t r ε=0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (beta_nonneg m t hε) (Ne.symm hz))).mpr
      (beta_succ_le m t hr hε)

/-- The gamma recurrence gives the quadratic high-frequency bound for the
ratio of the two actual capped radial norms. -/
theorem ratio_le_quadratic (m t : ℕ) {r ε : ℝ} (hr : 0<r) (hε : 0<ε)
    (hthreshold : 2*((m+2*t:ℕ)+1:ℝ)≤r*ε) :
    beta m (t+1) r ε / beta m t r ε ≤
      2*((m+2*t:ℕ)+1:ℝ)*((m+2*t:ℕ)+2:ℝ)/(r*ε)^2 := by
  let D := (1/ε)^(2*t)*((1/r)^(m+2*t+1)*((m+2*t).factorial:ℝ))/2
  have hD : 0<D := by dsimp [D]; positivity
  have hlow : D≤beta m t r ε := half_uncapped_le_beta m t hr hε hthreshold
  apply (div_le_iff₀ (hD.trans_le hlow)).mpr
  calc
    beta m (t+1) r ε ≤ (1/ε)^(2*(t+1))*(1/r)^(m+2*(t+1)+1)*((m+2*(t+1)).factorial:ℝ) :=
      beta_le_uncapped m (t+1) hr hε
    _ = (2*((m+2*t:ℕ)+1:ℝ)*((m+2*t:ℕ)+2:ℝ)/(r*ε)^2)*D := by
      dsimp [D]
      rw [show 2*(t+1)=2*t+2 by omega,
        show m+(2*t+2)=(m+2*t)+2 by omega]
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_add,pow_succ]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

#print axioms ratio_le_one
#print axioms ratio_le_quadratic
#print axioms half_uncapped_le_beta

end AsymptoticFourierNorm
