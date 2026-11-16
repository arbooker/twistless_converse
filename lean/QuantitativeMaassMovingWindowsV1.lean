module

public import QuantitativeMaassSmoothPacketDecayV1
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace QuantitativeMaass

def cosinePacket (φ : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s, φ s * (Real.cos (s*r) : ℂ)

def modulatedTimeTest (φ : ℝ → ℂ) (T : ℝ) (s : ℝ) : ℂ :=
  φ s * (Real.cos (s*T) : ℂ)

def scaledModulatedTimeTest (φ : ℝ → ℂ) (R T : ℝ) (s : ℝ) : ℂ :=
  φ (s/R) * (Real.cos (s*T) : ℂ)

/-- The constant is chosen for the fixed profile and exponent, before any
spectral parameter is chosen. The added one includes frequency zero. -/
theorem cosinePacket_rapid_decay (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ r : ℝ, (1+|r|)^k * ‖cosinePacket φ r‖ ≤ C := by
  obtain ⟨C₀,hC₀,h₀⟩ := compact_cosine_packet_power_decay φ hφ hc 0
  obtain ⟨Cₖ,hCₖ,hₖ⟩ := compact_cosine_packet_power_decay φ hφ hc k
  refine ⟨2^k*(C₀+Cₖ),by positivity,?_⟩
  intro r
  have hzero : ‖cosinePacket φ r‖ ≤ C₀ := by simpa [cosinePacket] using h₀ r
  have hpower : |r|^k * ‖cosinePacket φ r‖ ≤ Cₖ := by
    simpa [cosinePacket,Real.norm_eq_abs] using hₖ r
  by_cases hr : |r|≤1
  · have hp := pow_le_pow_left₀ (by positivity : 0≤1+|r|)
      (by linarith : 1+|r|≤2) k
    calc
      _ ≤ 2^k*‖cosinePacket φ r‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2^k*C₀ := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hp := pow_le_pow_left₀ (by positivity : 0≤1+|r|)
      (by linarith : 1+|r|≤2*|r|) k
    calc
      _ ≤ (2*|r|)^k*‖cosinePacket φ r‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2^k*(|r|^k*‖cosinePacket φ r‖) := by rw [mul_pow]; ring
      _ ≤ 2^k*Cₖ := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem cosinePacket_modulation (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (T r : ℝ) :
    cosinePacket (modulatedTimeTest φ T) r =
      (cosinePacket φ (r-T)+cosinePacket φ (r+T))/2 := by
  have hi (u : ℝ) : Integrable (fun s => φ s*(Real.cos (s*u):ℂ)) :=
    (show Continuous (fun s => φ s*(Real.cos (s*u):ℂ)) by fun_prop).integrable_of_hasCompactSupport hc.mul_right
  have hid (s : ℝ) :
      modulatedTimeTest φ T s*(Real.cos (s*r):ℂ) =
        (φ s*(Real.cos (s*(r-T)):ℂ)+φ s*(Real.cos (s*(r+T)):ℂ))/2 := by
    have hreal : Real.cos (s*T)*Real.cos (s*r) =
        (Real.cos (s*(r-T))+Real.cos (s*(r+T)))/2 := by
      rw [mul_sub,mul_add,Real.cos_sub,Real.cos_add]
      ring
    have hcomplex : (Real.cos (s*T):ℂ)*(Real.cos (s*r):ℂ) =
        ((Real.cos (s*(r-T)):ℂ)+(Real.cos (s*(r+T)):ℂ))/2 := by
      exact_mod_cast hreal
    dsimp [modulatedTimeTest]
    rw [mul_assoc,hcomplex]
    ring
  unfold cosinePacket
  simp_rw [hid]
  rw [integral_div,integral_add (hi _) (hi _)]

/-- Moving the center does not change the rapid-decay constant. -/
theorem modulated_cosinePacket_uniform_decay (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ T r : ℝ,
      ‖cosinePacket (modulatedTimeTest φ T) r‖ ≤
        C/(1+|r-T|)^k+C/(1+|r+T|)^k := by
  obtain ⟨C,hC,h⟩ := cosinePacket_rapid_decay φ hφ hc k
  refine ⟨C,hC,?_⟩
  intro T r
  have hbound (u : ℝ) : ‖cosinePacket φ u‖≤C/(1+|u|)^k :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h u)
  rw [cosinePacket_modulation φ hφ.continuous hc T r,norm_div,
    show ‖(2:ℂ)‖=2 by norm_num]
  have hn := norm_add_le (cosinePacket φ (r-T)) (cosinePacket φ (r+T))
  have hm := hbound (r-T)
  have hp := hbound (r+T)
  have hm0 := norm_nonneg (cosinePacket φ (r-T))
  have hp0 := norm_nonneg (cosinePacket φ (r+T))
  linarith

theorem cosinePacket_dilation (φ : ℝ → ℂ) (R r : ℝ) (hR : 0<R) :
    cosinePacket (fun s => φ (s/R)) r = (R:ℂ)*cosinePacket φ (R*r) := by
  have hid (s : ℝ) : (s/R)*(R*r)=s*r := by field_simp [hR.ne']
  unfold cosinePacket
  conv_lhs => arg 2; ext s; rw [← hid s]
  have hs := Measure.integral_comp_div
    (fun u => φ u*(Real.cos (u*(R*r)):ℂ)) R
  rw [abs_of_pos hR,Complex.real_smul] at hs
  exact hs

theorem scaledModulated_cosinePacket (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (R T r : ℝ) (hR : 0<R) :
    cosinePacket (scaledModulatedTimeTest φ R T) r =
      (R:ℂ)*((cosinePacket φ (R*(r-T))+cosinePacket φ (R*(r+T)))/2) := by
  have hid : scaledModulatedTimeTest φ R T =
      fun s => modulatedTimeTest φ (R*T) (s/R) := by
    funext s
    dsimp [scaledModulatedTimeTest,modulatedTimeTest]
    congr 2
    field_simp [hR.ne']
  rw [hid,cosinePacket_dilation _ R r hR,
    cosinePacket_modulation φ hφ hc (R*T) (R*r),mul_sub,mul_add]

/-- The same constant works for every positive time scale and every center.
Both peaks use the scaled distance from the moving frequencies. -/
theorem scaledModulated_cosinePacket_uniform_decay (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 0<R → ∀ T r : ℝ,
      ‖cosinePacket (scaledModulatedTimeTest φ R T) r‖ ≤
        C*R/(1+R*|r-T|)^k+C*R/(1+R*|r+T|)^k := by
  obtain ⟨C,hC,h⟩ := modulated_cosinePacket_uniform_decay φ hφ hc k
  refine ⟨C,hC,?_⟩
  intro R hR T r
  have hid : cosinePacket (scaledModulatedTimeTest φ R T) r =
      (R:ℂ)*cosinePacket (modulatedTimeTest φ (R*T)) (R*r) := by
    rw [scaledModulated_cosinePacket φ hφ.continuous hc R T r hR,
      cosinePacket_modulation φ hφ.continuous hc,mul_sub,mul_add]
  rw [hid,norm_mul,Complex.norm_real,Real.norm_of_nonneg hR.le]
  have hb := mul_le_mul_of_nonneg_left (h (R*T) (R*r)) hR.le
  rw [← mul_sub,← mul_add,abs_mul,abs_mul,abs_of_pos hR] at hb
  convert hb using 1
  ring

theorem smoothPacketMultiplier_principal (φ : ℝ → ℂ) (r : ℝ) :
    smoothPacketMultiplier φ (1/4+r^2) = cosinePacket φ r := by
  unfold smoothPacketMultiplier cosinePacket
  have he : (1/4+r^2)-1/4=r^2 := by ring
  simp only [he,Wave.signedCosine_nonneg_energy _ _ (sq_nonneg r),Real.sqrt_sq_eq_abs]
  apply integral_congr_ae
  filter_upwards with t
  rcases le_total 0 r with hr|hr
  · rw [abs_of_nonneg hr]
  · rw [abs_of_nonpos hr,mul_neg,Real.cos_neg]

/-- Uniform moving-window tails for the multiplier of the actual shifted
wave, in its original Friedrichs energy parameter. -/
theorem moving_smoothPacketMultiplier_uniform_decay (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 0<R → ∀ T r : ℝ,
      ‖smoothPacketMultiplier (scaledModulatedTimeTest φ R T) (1/4+r^2)‖ ≤
        C*R/(1+R*|r-T|)^k+C*R/(1+R*|r+T|)^k := by
  simpa only [smoothPacketMultiplier_principal] using
    scaledModulated_cosinePacket_uniform_decay φ hφ hc k

#print axioms cosinePacket_rapid_decay
#print axioms cosinePacket_modulation
#print axioms modulated_cosinePacket_uniform_decay
#print axioms cosinePacket_dilation
#print axioms scaledModulated_cosinePacket
#print axioms scaledModulated_cosinePacket_uniform_decay
#print axioms smoothPacketMultiplier_principal
#print axioms moving_smoothPacketMultiplier_uniform_decay

end QuantitativeMaass

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace QuantitativeMaass

/-- Average the modulations in the time variable, before applying the actual
wave multiplier. Restricted Lebesgue measure gives a spectral window. -/
def averagedTimeTest (φ : ℝ → ℂ) (R : ℝ) (μ : Measure ℝ) (s : ℝ) : ℂ :=
  ∫ T, scaledModulatedTimeTest φ R T s ∂μ

theorem scaled_modulation_product_integrable (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (R r : ℝ) (hR : 0<R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun z : ℝ × ℝ =>
      scaledModulatedTimeTest φ R z.1 z.2*(Real.cos (z.2*r):ℂ)) (μ.prod volume) := by
  have hi : Integrable (fun s => φ (s/R)) :=
    (integrable_comp_div_iff φ hR.ne').mpr (hφ.integrable_of_hasCompactSupport hc)
  have hmajor := hi.norm.comp_snd μ
  apply hmajor.mono'
  · exact (show Continuous (fun z : ℝ × ℝ =>
      scaledModulatedTimeTest φ R z.1 z.2*(Real.cos (z.2*r):ℂ)) by
        dsimp [scaledModulatedTimeTest]; fun_prop).aestronglyMeasurable
  · filter_upwards with z
    dsimp [scaledModulatedTimeTest]
    rw [norm_mul,norm_mul]
    have hm (x : ℝ) : ‖(Real.cos x:ℂ)‖≤1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one x
    calc
      _ ≤ (‖φ (z.2/R)‖*1)*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hm _) (norm_nonneg _))
          (hm _) (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- Fubini is justified from the compact time profile and finite window
measure; no summability or trace hypothesis is supplied. -/
theorem cosinePacket_average (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (R r : ℝ) (hR : 0<R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    cosinePacket (averagedTimeTest φ R μ) r =
      ∫ T, cosinePacket (scaledModulatedTimeTest φ R T) r ∂μ := by
  unfold cosinePacket averagedTimeTest
  simp_rw [← integral_mul_const]
  exact (integral_integral_swap
    (scaled_modulation_product_integrable φ hφ hc R r hR μ)).symm

theorem smoothPacketMultiplier_average (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (R r : ℝ) (hR : 0<R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    smoothPacketMultiplier (averagedTimeTest φ R μ) (1/4+r^2) =
      ∫ T, cosinePacket (scaledModulatedTimeTest φ R T) r ∂μ := by
  rw [smoothPacketMultiplier_principal,cosinePacket_average φ hφ hc R r hR μ]

/-- Rapid tails after averaging an arbitrary finite spectral window.
The constant is fixed before scale, window measure, frequency and distance. -/
theorem averaged_smoothPacketMultiplier_uniform_tail (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 0<R → ∀ (μ : Measure ℝ),
      IsFiniteMeasure μ → ∀ r d : ℝ, 0≤d →
      (∀ᵐ T ∂μ, d≤|r-T| ∧ d≤|r+T|) →
      ‖smoothPacketMultiplier (averagedTimeTest φ R μ) (1/4+r^2)‖ ≤
        (2*C*R/(1+R*d)^k)*μ.real univ := by
  obtain ⟨C,hC,h⟩ := scaledModulated_cosinePacket_uniform_decay φ hφ hc k
  refine ⟨C,hC,?_⟩
  intro R hR μ hμ r d hd hdist
  let : IsFiniteMeasure μ := hμ
  rw [smoothPacketMultiplier_average φ hφ.continuous hc R r hR μ]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hdist] with T hT
  have hden (x : ℝ) (hx : d≤|x|) :
      C*R/(1+R*|x|)^k ≤ C*R/(1+R*d)^k := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [mul_le_mul_of_nonneg_left hx hR.le]) k
  calc
    _ ≤ C*R/(1+R*|r-T|)^k+C*R/(1+R*|r+T|)^k := h R hR T r
    _ ≤ C*R/(1+R*d)^k+C*R/(1+R*d)^k := add_le_add (hden _ hT.1) (hden _ hT.2)
    _ = _ := by ring

/-- A literal interval window has its exact length as the averaging factor. -/
theorem interval_smoothPacketMultiplier_uniform_tail (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 0<R → ∀ a b r d : ℝ,
      a≤b → 0≤d → (∀ T∈Icc a b, d≤|r-T| ∧ d≤|r+T|) →
      ‖smoothPacketMultiplier (averagedTimeTest φ R (volume.restrict (Icc a b)))
        (1/4+r^2)‖ ≤ (2*C*R/(1+R*d)^k)*(b-a) := by
  obtain ⟨C,hC,h⟩ := averaged_smoothPacketMultiplier_uniform_tail φ hφ hc k
  refine ⟨C,hC,?_⟩
  intro R hR a b r d hab hd hdist
  have hm : ∀ᵐ T ∂volume.restrict (Icc a b), d≤|r-T| ∧ d≤|r+T| :=
    (ae_restrict_mem measurableSet_Icc).mono hdist
  have hb := h R hR (volume.restrict (Icc a b)) inferInstance r d hd hm
  simpa [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hb

#print axioms scaled_modulation_product_integrable
#print axioms cosinePacket_average
#print axioms smoothPacketMultiplier_average
#print axioms averaged_smoothPacketMultiplier_uniform_tail
#print axioms interval_smoothPacketMultiplier_uniform_tail

end QuantitativeMaass

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace QuantitativeMaass

theorem averagedTimeTest_charFun (φ : ℝ → ℂ) (R s : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    averagedTimeTest φ R μ s = φ (s/R)*((charFun μ s+charFun μ (-s))/2) := by
  have hi (u : ℝ) : Integrable (fun T : ℝ => Complex.exp ((u*T:ℝ)*Complex.I)) μ := by
    apply (integrable_const (1:ℝ)).mono'
    · exact (show Continuous (fun T : ℝ => Complex.exp ((u*T:ℝ)*Complex.I)) by
        fun_prop).aestronglyMeasurable
    · filter_upwards with T
      simp only [Complex.norm_exp_ofReal_mul_I,le_refl]
  have hid (T : ℝ) : (Real.cos (s*T):ℂ) =
      (Complex.exp ((s*T:ℝ)*Complex.I)+Complex.exp (((-s)*T:ℝ)*Complex.I))/2 := by
    rw [Complex.ofReal_cos]
    dsimp [Complex.cos]
    simp only [neg_mul,Complex.ofReal_neg]
  unfold averagedTimeTest scaledModulatedTimeTest
  rw [integral_const_mul]
  simp_rw [hid]
  rw [integral_div,integral_add (hi s) (hi (-s)),charFun_apply_real,charFun_apply_real]
  simp only [Complex.ofReal_mul]

theorem averagedTimeTest_smooth (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (R : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : ∀ k : ℕ, MemLp id k μ) :
    ContDiff ℝ ∞ (averagedTimeTest φ R μ) := by
  have hcf : ContDiff ℝ ∞ (charFun μ) := contDiff_charFun' hm
  have heq : averagedTimeTest φ R μ =
      fun s => φ (s/R)*((charFun μ s+charFun μ (-s))/2) :=
    funext (fun s => averagedTimeTest_charFun φ R s μ)
  rw [heq]
  fun_prop

theorem averagedTimeTest_compactSupport (φ : ℝ → ℂ) (hc : HasCompactSupport φ)
    (R : ℝ) (hR : 0<R) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    HasCompactSupport (averagedTimeTest φ R μ) := by
  have hs : HasCompactSupport (fun s => φ (s/R)) := by
    simpa only [Function.comp_def,Homeomorph.coe_mulRight₀,div_eq_mul_inv] using
      hc.comp_homeomorph (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero hR.ne'))
  have heq : averagedTimeTest φ R μ =
      fun s => φ (s/R)*((charFun μ s+charFun μ (-s))/2) :=
    funext (fun s => averagedTimeTest_charFun φ R s μ)
  rw [heq]
  exact hs.mul_right

/-- Every interval window has all the moments required for smoothness;
they are derived from the endpoints rather than supplied as hypotheses. -/
theorem interval_averagedTimeTest_smooth (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (R a b : ℝ) :
    ContDiff ℝ ∞ (averagedTimeTest φ R (volume.restrict (Icc a b))) := by
  apply averagedTimeTest_smooth φ hφ
  intro k
  exact memLp_of_bounded (ae_restrict_mem measurableSet_Icc)
    (show AEStronglyMeasurable id (volume.restrict (Icc a b)) from
      continuous_id.aestronglyMeasurable) k

theorem averagedTimeTest_support (φ : ℝ → ℂ)
    (hs : Function.support φ ⊆ Icc (-1) 1) (R : ℝ) (hR : 0<R) (μ : Measure ℝ) :
    Function.support (averagedTimeTest φ R μ) ⊆ Icc (-R) R := by
  intro s hmem
  have hn : φ (s/R)≠0 := by
    intro hz
    apply hmem
    simp only [averagedTimeTest,scaledModulatedTimeTest,hz,zero_mul,integral_zero]
  have hb := hs hn
  constructor
  · have hl := (le_div_iff₀ hR).mp hb.1
    linarith
  · have hu := (div_le_iff₀ hR).mp hb.2
    linarith

theorem averagedTimeTest_even (φ : ℝ → ℂ) (he : Function.Even φ)
    (R : ℝ) (μ : Measure ℝ) : Function.Even (averagedTimeTest φ R μ) := by
  intro s
  unfold averagedTimeTest scaledModulatedTimeTest
  simp only [neg_div,neg_mul,Real.cos_neg]
  rw [he (s/R)]

theorem averagedTimeTest_real (φ : ℝ → ℝ) (R s : ℝ) (μ : Measure ℝ) :
    averagedTimeTest (fun u => (φ u:ℂ)) R μ s =
      ((∫ T,φ (s/R)*Real.cos (s*T) ∂μ):ℝ) := by
  unfold averagedTimeTest scaledModulatedTimeTest
  simp only [← Complex.ofReal_mul]
  exact integral_complex_ofReal

/-- These are actual admissible smooth compact packets, so their multipliers
are summable on genuine cuspidal eigenfamilies by the existing spectral theorem. -/
theorem interval_averaged_packet_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (R a b : ℝ) (hR : 0<R) :
    Summable (fun i => ‖smoothPacketMultiplier
      (averagedTimeTest φ R (volume.restrict (Icc a b))) (e i)‖) := by
  exact cuspidal_smooth_packet_summable N hN v hv hcusp e he hgraph _
    (interval_averagedTimeTest_smooth φ hφ R a b)
    (averagedTimeTest_compactSupport φ hc R hR _)

#print axioms averagedTimeTest_charFun
#print axioms averagedTimeTest_smooth
#print axioms averagedTimeTest_compactSupport
#print axioms interval_averagedTimeTest_smooth
#print axioms averagedTimeTest_support
#print axioms averagedTimeTest_even
#print axioms averagedTimeTest_real
#print axioms interval_averaged_packet_summable

end QuantitativeMaass
