module

public import QuantitativeMaassCuspSpectralSummabilityV1
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace QuantitativeMaass

/-- The scalar multiplier of the actual shifted wave packet. -/
def smoothPacketMultiplier (φ : ℝ → ℂ) (e : ℝ) : ℂ :=
  ∫ t,φ t*(Wave.signedCosine t (e-1/4):ℂ)

theorem compact_cosine_packet_fourier (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (r : ℝ) :
    (∫ t,φ t*(Real.cos (t*r):ℂ))=
      (𝓕 (hc.toSchwartzMap hφ) (-r/(2*Real.pi))+
        𝓕 (hc.toSchwartzMap hφ) (r/(2*Real.pi)))/2 := by
  let p := fun s t : ℝ => Complex.exp ((t*s:ℝ)*Complex.I)*φ t
  have hi (s : ℝ) : Integrable (p s) :=
    (show Continuous (p s) by dsimp [p]; fun_prop).integrable_of_hasCompactSupport hc.mul_left
  have hfourier (s : ℝ) : (∫ t,p s t)=𝓕 (hc.toSchwartzMap hφ) (-s/(2*Real.pi)) := by
    change _=𝓕 φ (-s/(2*Real.pi))
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with t
    have he : -2*Real.pi*t*(-s/(2*Real.pi))=t*s := by field_simp
    simp only [p,he,smul_eq_mul]
  have hp (t : ℝ) : φ t*(Real.cos (t*r):ℂ)=(p r t+p (-r) t)/2 := by
    rw [Complex.ofReal_cos]
    dsimp [Complex.cos,p]
    rw [mul_neg,Complex.ofReal_neg]
    ring
  simp_rw [hp]
  rw [integral_div,integral_add (hi r) (hi (-r)),hfourier r,hfourier (-r),neg_neg]

theorem fourier_scaled_power_bound (f : SchwartzMap ℝ ℂ) (k : ℕ) (r : ℝ) :
    ‖r‖^k*‖f (r/(2*Real.pi))‖≤(SchwartzMap.seminorm ℝ k 0 f)*(2*Real.pi)^k := by
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (r/(2*Real.pi))
  rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi),div_pow,
    div_mul_eq_mul_div] at h
  exact (div_le_iff₀ (pow_pos (by positivity : 0<2*Real.pi) k)).mp h

/-- Arbitrarily high polynomial decay of an actual compact smooth cosine
packet, obtained from the Schwartz Fourier transform. -/
theorem compact_cosine_packet_power_decay (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ r : ℝ,‖r‖^k*‖∫ t,φ t*(Real.cos (t*r):ℂ)‖≤C := by
  let f : SchwartzMap ℝ ℂ := 𝓕 (hc.toSchwartzMap hφ)
  let C := (SchwartzMap.seminorm ℝ k 0 f)*(2*Real.pi)^k
  have hC : 0≤C := mul_nonneg (apply_nonneg _ _) (by positivity)
  refine ⟨C+1,by positivity,?_⟩
  intro r
  have hp := fourier_scaled_power_bound f k r
  have hm := fourier_scaled_power_bound f k (-r)
  rw [norm_neg] at hm
  rw [compact_cosine_packet_fourier φ hφ hc r]
  change ‖r‖^k*‖(f (-r/(2*Real.pi))+f (r/(2*Real.pi)))/2‖≤C+1
  rw [norm_div,show ‖(2:ℂ)‖=2 by norm_num]
  have h := mul_le_mul_of_nonneg_left
    (norm_add_le (f (-r/(2*Real.pi))) (f (r/(2*Real.pi)))) (pow_nonneg (norm_nonneg r) k)
  change ‖r‖^k*‖f (r/(2*Real.pi))‖≤C at hp
  change ‖r‖^k*‖f (-r/(2*Real.pi))‖≤C at hm
  nlinarith only [h,hp,hm]

/-- High-energy decay in the original nonnegative Friedrichs parameter. -/
theorem smoothPacketMultiplier_high_energy (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∃ C : ℝ,0<C ∧ ∀ e : ℝ,1≤e → (e+1)^8*‖smoothPacketMultiplier φ e‖≤C := by
  obtain ⟨C,hC,h⟩ := compact_cosine_packet_power_decay φ hφ hc 16
  refine ⟨3^8*C,by positivity,?_⟩
  intro e he
  have he0 : 0≤e-1/4 := by linarith
  have hid : ‖Real.sqrt (e-1/4)‖^16=(e-1/4)^8 := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),show (16:ℕ)=2*8 by decide,
      pow_mul,Real.sq_sqrt he0]
  have hm : smoothPacketMultiplier φ e=
      ∫ t,φ t*(Real.cos (t*Real.sqrt (e-1/4)):ℂ) := by
    unfold smoothPacketMultiplier
    simp only [Wave.signedCosine_nonneg_energy _ _ he0]
  have hs := h (Real.sqrt (e-1/4))
  rw [hid,←hm] at hs
  have hp := pow_le_pow_left₀ (by linarith : 0≤e+1)
    (by linarith : e+1≤3*(e-1/4)) 8
  calc
    _ ≤ (3*(e-1/4))^8*‖smoothPacketMultiplier φ e‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 3^8*((e-1/4)^8*‖smoothPacketMultiplier φ e‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Every smooth compact time packet has absolutely summable multipliers
on any actual orthonormal cuspidal eigenfamily. Low energies are handled by
the proved finite-band theorem, without a separate exceptional hypothesis. -/
theorem cuspidal_smooth_packet_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Summable (fun i => ‖smoothPacketMultiplier φ (e i)‖) := by
  classical
  obtain ⟨C,hC,hdecay⟩ := smoothPacketMultiplier_high_energy φ hφ hc
  obtain ⟨B,hB,hbands⟩ := cuspidal_spectral_band_polynomial N hN
  have hlow := (hbands ι v hv hcusp e he hgraph 1 (by norm_num)).1
  let f : ι → ℝ := fun i => ‖smoothPacketMultiplier φ (e i)‖
  have hmajor : Summable (fun i => C/(e i+1)^8) := by
    simpa only [mul_one_div] using
      (cuspidal_inverse_eighth_summable N hN v hv hcusp e he hgraph).mul_left C
  have hhi : Summable (fun i => if e i≤1 then 0 else f i) := by
    apply Summable.of_nonneg_of_le (fun i => by dsimp [f]; split_ifs <;> positivity) _ hmajor
    intro i
    have hei := he i
    split_ifs with hle
    · positivity
    · exact (le_div_iff₀ (by positivity : 0<(e i+1)^8)).mpr
        (by simpa only [mul_comm] using hdecay (e i) (le_of_lt (lt_of_not_ge hle)))
  have hlo : Summable (fun i => if e i≤1 then f i else 0) := by
    apply summable_of_hasFiniteSupport
    apply hlow.subset
    intro i hi
    by_contra hn
    change ¬e i≤1 at hn
    exact hi (ite_eq_right hn)
  have h := hlo.add hhi
  simpa only [ite_add_ite,add_zero,zero_add,ite_self] using h

#print axioms compact_cosine_packet_fourier
#print axioms fourier_scaled_power_bound
#print axioms compact_cosine_packet_power_decay
#print axioms smoothPacketMultiplier_high_energy
#print axioms cuspidal_smooth_packet_summable

end QuantitativeMaass
