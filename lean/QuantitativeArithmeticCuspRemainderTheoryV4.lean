module

public import QuantitativeArithmeticLogSectorPropagationV1
public import SmallLevelFourierBoundaryBoundV1

/-! Consolidated chapter: QuantitativeArithmeticCuspRemainder. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticCuspRemainderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCuspRemainder
open Complex Set FinitenessFourierConstruction FinitenessPolynomialSeries
open QuantitativeArithmeticLogSector

def remainder (A : ℕ → ℂ) (c : ℝ) (k : ℕ) (r w : ℂ) : ℂ :=
  fourier A ((c:ℂ)+w)-((-I*w)^k)⁻¹*r

theorem remainder_differentiableAt {A : ℕ → ℂ} (hA : PolynomialBound A)
    (c : ℝ) (k : ℕ) (r w : ℂ) (hw : 0<w.im) :
    DifferentiableAt ℂ (remainder A c k r) w := by
  have hn : w≠0 := by intro h; simp [h] at hw
  have hf := (FinitenessFourierConstruction.holomorphic hA (by simpa using hw : 0<((c:ℂ)+w).im)).comp w
    ((differentiableAt_const (c:ℂ)).add differentiableAt_id)
  apply hf.sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.inv
  · fun_prop
  · exact pow_ne_zero k (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hn)

theorem remainder_norm_bound {A : ℕ → ℂ} (hA : PolynomialBound A) (hA0 : A 0=0)
    (c : ℝ) (k : ℕ) (r : ℂ) :
    ∃ K : ℕ,∃ C : ℝ,0≤C ∧ ∀ w : ℂ,0<w.im →
      ‖remainder A c k r w‖≤C/w.im^K+‖r‖/‖w‖^k := by
  obtain ⟨K,C,hC,h⟩ := SmallLevelTaylor.fourier_boundary_bound hA hA0
  refine ⟨K,C,hC,?_⟩
  intro w hw
  apply (norm_sub_le _ _).trans
  have hf := h ((c:ℂ)+w) (by simpa using hw)
  simp only [add_im,ofReal_im,zero_add] at hf
  have hp : ‖((-I*w)^k)⁻¹*r‖=‖r‖/‖w‖^k := by
    simp only [norm_mul,norm_inv,norm_pow,norm_neg,norm_I,one_mul,div_eq_mul_inv]
    ring
  rw [hp]
  exact add_le_add hf le_rfl

theorem logRay_im (z : ℂ) : (logRay z).im=Real.exp (-z.im)*Real.sin z.re := by
  simp [logRay,Complex.exp_im,Complex.mul_re,Complex.mul_im]

theorem logRay_norm (z : ℂ) : ‖logRay z‖=Real.exp (-z.im) := by
  simp [logRay,Complex.norm_exp,Complex.mul_re]

theorem logRay_positive {z : ℂ} (hz : 0<z.re ∧ z.re<Real.pi) : 0<(logRay z).im := by
  rw [logRay_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

theorem log_remainder_strip_holomorphic {A : ℕ → ℂ} (hA : PolynomialBound A)
    (c : ℝ) (k : ℕ) (r : ℂ) (a b : ℝ) (ha : 0<a) (_hab : a<b) (hb : b<Real.pi) :
    DiffContOnCl ℂ (fun z => remainder A c k r (logRay z)) (HadamardThreeLines.verticalStrip a b) := by
  have hdiff (z : ℂ) (hz : a≤z.re ∧ z.re≤b) :
      DifferentiableAt ℂ (fun z => remainder A c k r (logRay z)) z := by
    apply (remainder_differentiableAt hA c k r _ (logRay_positive ⟨by linarith,by linarith⟩)).comp
    unfold logRay
    fun_prop
  have hc : IsClosed {z : ℂ | a≤z.re ∧ z.re≤b} :=
    (isClosed_le continuous_const continuous_re).inter (isClosed_le continuous_re continuous_const)
  have hsub : closure (HadamardThreeLines.verticalStrip a b)⊆{z : ℂ | a≤z.re ∧ z.re≤b} := by
    apply closure_minimal _ hc
    intro z hz
    exact ⟨hz.1.le,hz.2.le⟩
  exact ⟨fun z hz => (hdiff z ⟨hz.1.le,hz.2.le⟩).differentiableWithinAt,
    fun z hz => (hdiff z (hsub hz)).continuousAt.continuousWithinAt⟩

#print axioms remainder_norm_bound
#print axioms log_remainder_strip_holomorphic
end QuantitativeArithmeticCuspRemainder
end
end

/-! ## QuantitativeArithmeticCuspLogGrowthV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCuspRemainder
open Complex Set FinitenessFourierConstruction FinitenessPolynomialSeries
open QuantitativeArithmeticLogSector

theorem sin_inverse_power_bound (a b : ℝ) (ha : 0<a) (_hab : a<b) (hb : b<Real.pi) (K : ℕ) :
    ∃ M : ℝ,0≤M ∧ ∀ x : ℝ,a≤x → x≤b → ((Real.sin x)^K)⁻¹≤M := by
  have hsin (x : ℝ) (hx : x∈Icc a b) : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  have hc : ContinuousOn (fun x : ℝ => ((Real.sin x)^K)⁻¹) (Icc a b) :=
    (Real.continuous_sin.pow K).continuousOn.inv₀ (fun x hx => pow_ne_zero K (hsin x hx).ne')
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x hxa hxb
  have h := hM x ⟨hxa,hxb⟩
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pow_pos (hsin x ⟨hxa,hxb⟩) K))] at h
  exact h.trans (le_max_left _ _)

theorem inverse_exp_neg_power (t : ℝ) (j : ℕ) : (Real.exp (-t)^j)⁻¹=Real.exp ((j:ℝ)*t) := by
  rw [← Real.exp_nat_mul,← Real.exp_neg]
  congr 1
  ring

theorem log_remainder_growth {A : ℕ → ℂ} (hA : PolynomialBound A) (hA0 : A 0=0)
    (c : ℝ) (k : ℕ) (r : ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b) (hb : b<Real.pi) :
    ∃ C B : ℝ,0≤C ∧ 0≤B ∧ ∀ z : ℂ,a≤z.re → z.re≤b →
      ‖remainder A c k r (logRay z)‖≤C*Real.exp (B*|z.im|) := by
  obtain ⟨K,C,hC,h⟩ := remainder_norm_bound hA hA0 c k r
  obtain ⟨M,hM,hM'⟩ := sin_inverse_power_bound a b ha hab hb K
  refine ⟨C*M+‖r‖,(K:ℝ)+(k:ℝ),by positivity,by positivity,?_⟩
  intro z hza hzb
  have hz : 0<z.re ∧ z.re<Real.pi := ⟨by linarith,by linarith⟩
  have hh := h (logRay z) (logRay_positive hz)
  rw [logRay_im,logRay_norm,mul_pow,div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev,
    inverse_exp_neg_power,inverse_exp_neg_power] at hh
  have hs := hM' z.re hza hzb
  have hK : (K:ℝ)*z.im≤((K:ℝ)+(k:ℝ))*|z.im| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self z.im) (Nat.cast_nonneg (α:=ℝ) K)
    nlinarith [abs_nonneg z.im,Nat.cast_nonneg (α:=ℝ) k]
  have hk : (k:ℝ)*z.im≤((K:ℝ)+(k:ℝ))*|z.im| := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self z.im) (Nat.cast_nonneg (α:=ℝ) k)
    nlinarith [abs_nonneg z.im,Nat.cast_nonneg (α:=ℝ) K]
  have hsin0 : 0≤((Real.sin z.re)^K)⁻¹ := inv_nonneg.mpr (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2).le K)
  have hfirst : C*(((Real.sin z.re)^K)⁻¹*Real.exp ((K:ℝ)*z.im))≤
      C*(M*Real.exp (((K:ℝ)+(k:ℝ))*|z.im|)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact mul_le_mul hs (Real.exp_le_exp.mpr hK) (Real.exp_pos _).le hM
  have hsecond := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hk) (norm_nonneg r)
  nlinarith
#print axioms log_remainder_growth
end QuantitativeArithmeticCuspRemainder
end
end

/-! ## QuantitativeArithmeticCuspLogVerticalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCuspRemainder
open Complex FinitenessFourierConstruction
open QuantitativeArithmeticLogSector

theorem logRay_vertical (z : ℂ) (hz : z.re=Real.pi/2) :
    logRay z=(Real.exp (-z.im):ℂ)*I := by
  apply Complex.ext <;> simp [logRay,Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,hz]

theorem vertical_log_decay (A : ℕ → ℂ) (c : ℝ) (k : ℕ) (r : ℂ)
    (h : ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ y : ℝ,0<y →
      ‖fourier A ((c:ℂ)+(y:ℂ)*I)-(y:ℂ)^(-(k:ℂ))*r‖≤C*y^(n:ℝ)) :
    ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ z : ℂ,z.re=Real.pi/2 →
      ‖remainder A c k r (logRay z)‖≤C*Real.exp (-(n:ℝ)*z.im) := by
  intro n
  obtain ⟨C,hC,h⟩ := h n
  refine ⟨C,hC,?_⟩
  intro z hz
  have hh := h (Real.exp (-z.im)) (Real.exp_pos _)
  have he (y : ℝ) : -I*((y:ℂ)*I)=(y:ℂ) := by
    calc
      _ = -(y:ℂ)*(I*I) := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [logRay_vertical z hz,remainder,he]
  rw [Complex.cpow_neg,Complex.cpow_natCast,Real.rpow_natCast,← Real.exp_nat_mul] at hh
  have hexp : (n:ℝ)*(-z.im)= -(n:ℝ)*z.im := by ring
  rwa [hexp] at hh
#print axioms vertical_log_decay
end QuantitativeArithmeticCuspRemainder
end
end
