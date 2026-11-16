module

public import QuantitativeMaassAbelOscillatoryAmplitudeV1
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The slowly varying amplitude after removing the central frequency. -/
def windowCarrier (φ : ℝ → ℂ) (R ε s : ℝ) : ℂ :=
  φ (s/R)*charFun (volume.restrict (Icc (-ε) ε)) s

theorem interval_charFun_moments (a b : ℝ) (n : ℕ) :
    MemLp id n (volume.restrict (Icc a b)) :=
  memLp_of_bounded (ae_restrict_mem measurableSet_Icc)
    continuous_id.aestronglyMeasurable n

theorem interval_charFun_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (charFun (volume.restrict (Icc a b))) :=
  contDiff_charFun' (interval_charFun_moments a b)

/-- All derivatives of the centered interval characteristic function have
norm at most its length when the half-width is at most one. -/
theorem interval_charFun_derivative_bound (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (n : ℕ) (s : ℝ) :
    ‖iteratedDeriv n (charFun (volume.restrict (Icc (-ε) ε))) s‖≤2*ε := by
  rw [iteratedDeriv_charFun (interval_charFun_moments (-ε) ε n),norm_mul,
    norm_pow,Complex.norm_I,one_pow,one_mul]
  have h : ‖∫ x : ℝ, (x:ℂ)^n*Complex.exp ((s:ℂ)*x*Complex.I)
      ∂volume.restrict (Icc (-ε) ε)‖≤
      1*(volume.restrict (Icc (-ε) ε)).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hx1 : |x|≤1 := (abs_le.mpr hx).trans hε1
    rw [norm_mul,norm_pow,← Complex.ofReal_mul,Complex.norm_exp_ofReal_mul_I,
      mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg x) hx1
  rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (by linarith),one_mul] at h
  convert h using 1
  ring

theorem windowCarrier_smooth (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (R ε : ℝ) :
    ContDiff ℝ ∞ (windowCarrier φ R ε) := by
  have hc := interval_charFun_smooth (-ε) ε
  change ContDiff ℝ ∞ (fun s => φ (s/R)*charFun (volume.restrict (Icc (-ε) ε)) s)
  fun_prop

theorem windowCarrier_compact (φ : ℝ → ℂ) (hc : HasCompactSupport φ)
    (R ε : ℝ) (hR : 0<R) : HasCompactSupport (windowCarrier φ R ε) := by
  have hs : HasCompactSupport (fun s => φ (s/R)) := by
    simpa only [Function.comp_def,Homeomorph.coe_mulRight₀,div_eq_mul_inv] using
      hc.comp_homeomorph (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero hR.ne'))
  exact hs.mul_right

/-- Dilation by R>=1 does not increase any of the fixed finite family of
smooth compact-profile derivative bounds. -/
theorem compact_dilated_derivative_bounds (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (m : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,1≤R → ∀ n : ℕ,n≤m → ∀ s : ℝ,
      ‖iteratedDeriv n (fun u => φ (u/R)) s‖≤C := by
  obtain ⟨C,hC0,hC⟩ := hc.exists_bound_iteratedFDeriv hφ m
  refine ⟨C,hC0,?_⟩
  intro R hR n hn s
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hid : (fun u : ℝ => φ (u/R))=(fun u => φ (R⁻¹*u)) := by
    funext u
    congr 1
    ring
  rw [hid,iteratedDeriv_comp_const_smul (hφ.of_le (by simp)) R⁻¹]
  dsimp only
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hRp.le) n)]
  have hb : (R⁻¹)^n≤1 := pow_le_one₀ (inv_nonneg.mpr hRp.le) ((inv_le_one₀ hRp).mpr hR)
  have hh := hC n hn (R⁻¹*s)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  exact (mul_le_mul hb hh (norm_nonneg _) zero_le_one).trans_eq (one_mul C)

/-- One constant is chosen before R, epsilon and time. The original carrier
and every derivative through a prescribed finite order are O(epsilon). -/
theorem windowCarrier_uniform_derivative_bounds (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (m : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,1≤R → ∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ n : ℕ,n≤m → ∀ s : ℝ,‖iteratedDeriv n (windowCarrier φ R ε) s‖≤C*ε := by
  obtain ⟨C,hC0,hC⟩ := compact_dilated_derivative_bounds φ hφ hc m
  refine ⟨(2:ℝ)^m*C*2,by positivity,?_⟩
  intro R hR ε hε hε1 n hn s
  have hdil : ContDiff ℝ n (fun u => φ (u/R)) := (hφ.of_le (by simp)).comp (by fun_prop)
  have hcf : ContDiff ℝ n (charFun (volume.restrict (Icc (-ε) ε))) :=
    (interval_charFun_smooth (-ε) ε).of_le (by simp)
  change ‖iteratedDeriv n (fun u => φ (u/R)*charFun (volume.restrict (Icc (-ε) ε)) u) s‖≤_
  rw [iteratedDeriv_fun_mul hdil.contDiffAt hcf.contDiffAt]
  calc
    _ ≤ ∑ i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i (fun u => φ (u/R)) s*
        iteratedDeriv (n-i) (charFun (volume.restrict (Icc (-ε) ε))) s‖ := norm_sum_le _ _
    _ ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*C*(2*ε) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i≤m := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hC R hR i him s) (by positivity))
        (interval_charFun_derivative_bound ε hε hε1 (n-i) s)
        (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^n*C*(2*ε) := by
      rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose]
      push_cast
      ring
    _ ≤ _ := by
      have hp : (2:ℝ)^n≤2^m := pow_le_pow_right₀ (by norm_num) hn
      nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hC0 hε)]

/-- Translation of an actual interval measure extracts its central phase. -/
theorem interval_charFun_translate (a b t s : ℝ) (hab : a≤b) :
    charFun (volume.restrict (Icc (a+t) (b+t))) s=
      charFun (volume.restrict (Icc a b)) s*Complex.exp ((s:ℂ)*t*Complex.I) := by
  have habt : a+t≤b+t := by linarith
  calc
    _ = ∫ v in (a+t)..(b+t),Complex.exp ((s:ℂ)*v*Complex.I) := by
      rw [charFun_apply_real,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le habt]
    _ = ∫ v in a..b,Complex.exp ((s:ℂ)*(v+t:ℝ)*Complex.I) :=
      (intervalIntegral.integral_comp_add_right (fun v : ℝ => Complex.exp ((s:ℂ)*v*Complex.I)) t).symm
    _ = (∫ v in a..b,Complex.exp ((s:ℂ)*v*Complex.I))*Complex.exp ((s:ℂ)*t*Complex.I) := by
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [Complex.ofReal_add,mul_add,add_mul,Complex.exp_add]
    _ = _ := by
      rw [charFun_apply_real,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]

/-- Exact carrier decomposition of the ORIGINAL symmetric window time test.
Both frequency signs use the same amplitude, reflected for the negative sign. -/
theorem symmetricWindowTimeTest_carriers (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (R t ε s : ℝ) (hε : 0≤ε) :
    symmetricWindowTimeTest K R (t-ε) (t+ε) s=
      Complex.exp ((t*s:ℝ)*Complex.I)*windowCarrier (kernelTimeProfile K) R ε s+
      Complex.exp (((-t)*s:ℝ)*Complex.I)*windowCarrier (kernelTimeProfile K) R ε (-s) := by
  have htr (u : ℝ) : charFun (volume.restrict (Icc (t-ε) (t+ε))) u=
      charFun (volume.restrict (Icc (-ε) ε)) u*Complex.exp ((u:ℂ)*t*Complex.I) := by
    have hh := interval_charFun_translate (-ε) ε t u (by linarith)
    simpa only [add_comm ε t,neg_add_eq_sub] using hh
  rw [symmetricWindowTimeTest,averagedTimeTest_charFun,htr s,htr (-s)]
  have heφ := kernelTimeProfile_even K he (s/R)
  simp only [windowCarrier,neg_div,heφ,Complex.ofReal_neg,Complex.ofReal_mul]
  have hp : ((-s:ℂ)*(t:ℂ)*Complex.I)=(((-t:ℝ):ℂ)*(s:ℂ)*Complex.I) := by push_cast;ring
  rw [hp]
  have hp' : ((s:ℂ)*(t:ℂ)*Complex.I)=((t:ℂ)*(s:ℂ)*Complex.I) := by ring
  rw [hp']
  simp only [Complex.ofReal_neg]
  ring

/-- The amplitude has the same dilation support as the fixed time profile. -/
theorem windowCarrier_support (φ : ℝ → ℂ) (B R ε : ℝ) (hR : 0<R)
    (hs : Function.support φ⊆Icc (-B) B) :
    Function.support (windowCarrier φ R ε)⊆Icc (-(B*R)) (B*R) := by
  intro s hn
  have hnφ : φ (s/R)≠0 := by
    intro hz
    exact hn (by simp only [windowCarrier,hz,zero_mul])
  have hb := hs hnφ
  constructor
  · have hh := (le_div_iff₀ hR).mp hb.1
    linarith
  · exact (div_le_iff₀ hR).mp hb.2

/-- Original K: constants are fixed before the center, width, dilation and
time coordinate. Both carrier signs and all required derivatives are covered. -/
theorem kernel_windowCarrier_uniform_bounds (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (m : ℕ) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ R : ℝ,1≤R → ∀ ε : ℝ,0≤ε → ε≤1 →
      Function.support (windowCarrier (kernelTimeProfile K) R ε)⊆Icc (-(B*R)) (B*R) ∧
      ∀ n : ℕ,n≤m → ∀ s : ℝ,
        ‖iteratedDeriv n (windowCarrier (kernelTimeProfile K) R ε) s‖≤C*ε ∧
        ‖iteratedDeriv n (fun u => windowCarrier (kernelTimeProfile K) R ε (-u)) s‖≤C*ε := by
  have hφ := kernelTimeProfile_smooth K
  have hφc := kernelTimeProfile_compact K hc
  obtain ⟨B,hB,hBs⟩ := hφc.isCompact.isBounded.subset_closedBall_lt 0 (0:ℝ)
  have hs : Function.support (kernelTimeProfile K)⊆Icc (-B) B := by
    intro s hs
    have hb := hBs (subset_tsupport _ hs)
    have hh : |s|≤B := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hb
    exact abs_le.mp hh
  obtain ⟨C,hC,hbound⟩ := windowCarrier_uniform_derivative_bounds _ hφ hφc m
  refine ⟨B,C+1,hB,by linarith,?_⟩
  intro R hR ε hε hε1
  refine ⟨windowCarrier_support _ B R ε (lt_of_lt_of_le zero_lt_one hR) hs,?_⟩
  intro n hn s
  have hb (u : ℝ) : ‖iteratedDeriv n (windowCarrier (kernelTimeProfile K) R ε) u‖≤(C+1)*ε :=
    (hbound R hR ε hε hε1 n hn u).trans (by nlinarith)
  refine ⟨hb s,?_⟩
  rw [iteratedDeriv_comp_neg,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  exact hb (-s)

#print axioms windowCarrier_support
#print axioms kernel_windowCarrier_uniform_bounds

#print axioms interval_charFun_moments
#print axioms interval_charFun_smooth
#print axioms interval_charFun_derivative_bound
#print axioms windowCarrier_smooth
#print axioms windowCarrier_compact
#print axioms compact_dilated_derivative_bounds
#print axioms windowCarrier_uniform_derivative_bounds
#print axioms interval_charFun_translate
#print axioms symmetricWindowTimeTest_carriers

end QuantitativeMaass
