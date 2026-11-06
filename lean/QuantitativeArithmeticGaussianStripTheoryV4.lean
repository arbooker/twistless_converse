module

public import FinitenessBoundaryDecayV1
public import FinitenessMellinContourV1
public import Mathlib.Analysis.Complex.Hadamard
public import QuantitativeArithmeticSimplePoleContourV1
public import QuantitativeArithmeticSimplePoleEntirePartV1
public import QuantitativeArithmeticVerticalBoundedTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticGaussianStrip. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticGaussianPolynomialBoundV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex

/-- A Gaussian absorbs any fixed polynomial uniformly on a horizontal
bounded range of real parts. The bound is explicit and independent of a
vertical translation. -/
theorem gaussian_polynomial_bound (R : ℝ) (hR : 0≤R) (n : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ w : ℂ,|w.re|≤R →
      ‖exp (w^2)‖*(1+‖w‖)^n≤K := by
  refine ⟨Real.exp (R^2+1)*(R+2)^n*(n.factorial:ℝ),by positivity,?_⟩
  intro w hw
  have hu : |w.im|≤1+w.im^2 := by nlinarith [sq_nonneg (|w.im|-1),sq_abs w.im]
  have hn : 1+‖w‖≤(R+2)*(1+w.im^2) := by
    have hh := norm_le_abs_re_add_abs_im w
    nlinarith [sq_nonneg w.im]
  have hp := Real.pow_div_factorial_le_exp (1+w.im^2) (by positivity : 0≤1+w.im^2) n
  have hfac : 0<(n.factorial:ℝ) := by positivity
  have hp' : (1+w.im^2)^n≤Real.exp (1+w.im^2)*(n.factorial:ℝ) :=
    (div_le_iff₀ hfac).mp hp
  have hre : (w^2).re≤R^2-w.im^2 := by
    simp only [pow_two,Complex.mul_re]
    have hh := abs_le.mp hw
    nlinarith [hh.1,hh.2]
  rw [norm_exp]
  calc
    Real.exp (w^2).re*(1+‖w‖)^n ≤ Real.exp (R^2-w.im^2)*((R+2)*(1+w.im^2))^n := by
      apply mul_le_mul (Real.exp_le_exp.mpr hre)
        (pow_le_pow_left₀ (by positivity) hn n) (by positivity) (by positivity)
    _ = Real.exp (R^2-w.im^2)*(R+2)^n*(1+w.im^2)^n := by rw [mul_pow]; ring
    _ ≤ Real.exp (R^2-w.im^2)*(R+2)^n*(Real.exp (1+w.im^2)*(n.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left hp' (by positivity)
    _ = _ := by
      rw [show Real.exp (R^2-w.im^2)*(R+2)^n*(Real.exp (1+w.im^2)*(n.factorial:ℝ))=
        (Real.exp (R^2-w.im^2)*Real.exp (1+w.im^2))*(R+2)^n*(n.factorial:ℝ) by ring,
        ← Real.exp_add]
      congr 3
      ring

theorem one_add_norm_translate (z c : ℂ) :
    1+‖z‖≤(1+‖c‖)*(1+‖z-c‖) := by
  have hh : ‖z‖≤‖c‖+‖z-c‖ := by
    calc
      ‖z‖=‖c+(z-c)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  nlinarith [norm_nonneg c,norm_nonneg (z-c)]

theorem one_add_norm_center (z c : ℂ) :
    1+‖c‖≤(1+‖z‖)*(1+‖z-c‖) := by
  simpa only [norm_sub_rev] using one_add_norm_translate c z

#print axioms gaussian_polynomial_bound
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticGaussianLocalizationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex

def kernel (t : ℝ) (z : ℂ) : ℂ := exp ((z-(t:ℂ)*I)^2)

theorem kernel_differentiable (t : ℝ) : Differentiable ℂ (kernel t) := by
  unfold kernel
  fun_prop

theorem kernel_weight_bounds (R : ℝ) (hR : 0≤R) (n : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ t : ℝ,∀ z : ℂ,|z.re|≤R →
      ‖kernel t z‖*(1+‖z‖)^n≤K*(1+|t|)^n ∧
      (1+|t|)^n*‖kernel t z‖≤K*(1+‖z‖)^n := by
  obtain ⟨K,hK,h⟩ := gaussian_polynomial_bound R hR n
  refine ⟨K,hK,?_⟩
  intro t z hz
  have ht : ‖(t:ℂ)*I‖=|t| := by simp
  have hw : |(z-(t:ℂ)*I).re|≤R := by simpa using hz
  have hg := h (z-(t:ℂ)*I) hw
  change ‖kernel t z‖*(1+‖z-(t:ℂ)*I‖)^n≤K at hg
  have h1 := one_add_norm_translate z ((t:ℂ)*I)
  have h2 := one_add_norm_center z ((t:ℂ)*I)
  rw [ht] at h1 h2
  constructor
  · calc
      ‖kernel t z‖*(1+‖z‖)^n ≤ ‖kernel t z‖*((1+|t|)*(1+‖z-(t:ℂ)*I‖))^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 n) (norm_nonneg _)
      _ = (‖kernel t z‖*(1+‖z-(t:ℂ)*I‖)^n)*(1+|t|)^n := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hg (by positivity)
  · calc
      (1+|t|)^n*‖kernel t z‖ ≤ ((1+‖z‖)*(1+‖z-(t:ℂ)*I‖))^n*‖kernel t z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2 n) (norm_nonneg _)
      _ = (‖kernel t z‖*(1+‖z-(t:ℂ)*I‖)^n)*(1+‖z‖)^n := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hg (by positivity)

theorem kernel_center_norm (z : ℂ) : ‖kernel z.im z‖=Real.exp (z.re^2) := by
  have he : z-(z.im:ℂ)*I=(z.re:ℂ) := by apply Complex.ext <;> simp
  rw [kernel,he,norm_exp]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re]

theorem norm_le_kernel_center (F : ℂ → ℂ) (z : ℂ) :
    ‖F z‖≤‖kernel z.im z*F z‖ := by
  rw [norm_mul,kernel_center_norm]
  have hh : 1≤Real.exp (z.re^2) := Real.one_le_exp (sq_nonneg _)
  nlinarith [norm_nonneg (F z)]
#print axioms kernel_weight_bounds
#print axioms norm_le_kernel_center
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticGaussianExponentialBoundV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex

theorem kernel_norm_formula (T : ℝ) (z : ℂ) :
    ‖kernel T z‖=Real.exp (z.re^2-(z.im-T)^2) := by
  rw [kernel,norm_exp]
  congr 1
  simp [pow_two,Complex.mul_re,Complex.mul_im]

theorem kernel_signed_exponential (R A : ℝ) (_hR : 0≤R) :
    ∃ K : ℝ,0<K ∧ ∀ T : ℝ,∀ z : ℂ,|z.re|≤R →
      ‖kernel T z‖*Real.exp (A*z.im)≤K*Real.exp (A*T) := by
  refine ⟨Real.exp (R^2+A^2/4),Real.exp_pos _,?_⟩
  intro T z hz
  rw [kernel_norm_formula,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := pow_le_pow_left₀ (abs_nonneg z.re) hz 2
  rw [sq_abs] at hh
  nlinarith [sq_nonneg ((z.im-T)-A/2)]

theorem kernel_absolute_exponential (R A : ℝ) (_hR : 0≤R) (hA : 0≤A) :
    ∃ K : ℝ,0<K ∧ ∀ T : ℝ,∀ z : ℂ,|z.re|≤R →
      ‖kernel T z‖*Real.exp (A*|z.im|)≤K*Real.exp (A*|T|) := by
  refine ⟨Real.exp (R^2+A^2/4),Real.exp_pos _,?_⟩
  intro T z hz
  rw [kernel_norm_formula,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := pow_le_pow_left₀ (abs_nonneg z.re) hz 2
  rw [sq_abs] at hh
  have ht : |z.im|≤|T|+|z.im-T| := by
    calc
      |z.im|=|T+(z.im-T)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hm := mul_le_mul_of_nonneg_left ht hA
  have hs := sq_nonneg (|z.im-T|-A/2)
  have hsq := sq_abs (z.im-T)
  nlinarith
#print axioms kernel_signed_exponential
#print axioms kernel_absolute_exponential
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticExponentialThreeLinesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex Set

/-- Exponentially rapid decay on the right boundary propagates uniformly to
closed substrips bounded away from the left edge, under a fixed exponential
growth bound. Only holomorphy on this strip is used. -/
theorem exponential_right_propagation (F : ℂ → ℂ) (a b C B : ℝ)
    (hab : a<b) (hC : 0≤C) (hB : 0≤B)
    (hF : DiffContOnCl ℂ F (HadamardThreeLines.verticalStrip a b))
    (hg : ∀ z : ℂ,a≤z.re → z.re≤b → ‖F z‖≤C*Real.exp (B*|z.im|))
    (hr : ∀ n : ℕ,∃ D : ℝ,0≤D ∧ ∀ z : ℂ,z.re=b → ‖F z‖≤D*Real.exp (-(n:ℝ)*z.im))
    (l : ℝ) (hal : a<l) (_hlb : l≤b) :
    ∀ L : ℕ,∃ K : ℝ,0≤K ∧ ∀ z : ℂ,l≤z.re → z.re≤b → 0≤z.im →
      ‖F z‖≤K*Real.exp (-(L:ℝ)*z.im) := by
  let R : ℝ := |a|+|b|
  have hR : 0≤R := by dsimp [R]; positivity
  have hre (z : ℂ) (hz : a≤z.re ∧ z.re≤b) : |z.re|≤R := by
    apply abs_le.mpr
    dsimp [R]
    constructor <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b,hz.1,hz.2]
  let θ₀ : ℝ := (l-a)/(b-a)
  have hθ₀ : 0<θ₀ := div_pos (sub_pos.mpr hal) (sub_pos.mpr hab)
  obtain ⟨K₀,hK₀,hleft⟩ := kernel_absolute_exponential R B hR hB
  intro L
  obtain ⟨n,hn⟩ := exists_nat_gt ((B+(L:ℝ))/θ₀)
  have hnθ : B+(L:ℝ)<(n:ℝ)*θ₀ := (div_lt_iff₀ hθ₀).mp hn
  obtain ⟨D,hD,hr⟩ := hr n
  obtain ⟨K₁,hK₁,hright⟩ := kernel_signed_exponential R (-(n:ℝ)) hR
  let A : ℝ := K₀*C+1
  let E : ℝ := K₁*D+1
  have hA : 1≤A := by dsimp [A]; nlinarith
  have hE : 1≤E := by dsimp [E]; nlinarith
  refine ⟨A*E,by positivity,?_⟩
  intro z hzl hzb hzi
  let θ : ℝ := (z.re-a)/(b-a)
  have hθ : 0≤θ ∧ θ≤1 := by
    dsimp [θ]
    constructor
    · exact div_nonneg (by linarith) (sub_pos.mpr hab).le
    · apply (div_le_one (sub_pos.mpr hab)).mpr
      linarith
  have hθmin : θ₀≤θ := div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hab).le
  let G : ℂ → ℂ := fun w => kernel z.im w*F w
  have hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip a b) :=
    ⟨(kernel_differentiable z.im).differentiableOn.mul hF.1,
      (kernel_differentiable z.im).continuous.continuousOn.mul hF.2⟩
  have hbound (w : ℂ) (hw : a≤w.re ∧ w.re≤b) :
      ‖G w‖≤A*Real.exp (B*z.im) := by
    dsimp only [G]
    rw [norm_mul]
    have h1 := mul_le_mul_of_nonneg_left (hg w hw.1 hw.2) (norm_nonneg (kernel z.im w))
    have h2 := mul_le_mul_of_nonneg_left (hleft z.im w (hre w hw)) hC
    rw [abs_of_nonneg hzi] at h2
    dsimp [A]
    nlinarith [Real.exp_pos (B*z.im)]
  have hbdd : BddAbove ((norm ∘ G) '' HadamardThreeLines.verticalClosedStrip a b) := by
    refine ⟨A*Real.exp (B*z.im),?_⟩
    rintro v ⟨w,hw,rfl⟩
    exact hbound w hw
  have hright' (w : ℂ) (hw : w.re=b) : ‖G w‖≤E*Real.exp (-(n:ℝ)*z.im) := by
    dsimp only [G]
    rw [norm_mul]
    have h1 := mul_le_mul_of_nonneg_left (hr w hw) (norm_nonneg (kernel z.im w))
    have h2 := mul_le_mul_of_nonneg_left (hright z.im w (hre w ⟨by linarith,hw.le⟩)) hD
    dsimp [E]
    nlinarith [Real.exp_pos (-(n:ℝ)*z.im)]
  have hh := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab
    (show z∈HadamardThreeLines.verticalClosedStrip a b from ⟨by linarith,hzb⟩) hG hbdd
    (fun w hw => by change w.re=a at hw; exact hbound w ⟨hw.ge,by linarith⟩)
    (fun w hw => hright' w hw)
  change ‖G z‖≤(A*Real.exp (B*z.im))^(1-θ)*(E*Real.exp (-(n:ℝ)*z.im))^θ at hh
  have haθ : A^(1-θ)≤A := by
    have ht := Real.rpow_le_rpow_of_exponent_le hA (by linarith [hθ.1] : 1-θ≤1)
    simpa only [Real.rpow_one] using ht
  have heθ : E^θ≤E := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hE hθ.2
  have hexponent : B*z.im*(1-θ)+(-(n:ℝ)*z.im)*θ≤-(L:ℝ)*z.im := by
    have hnθ' := mul_le_mul_of_nonneg_left hθmin (Nat.cast_nonneg (α:=ℝ) n)
    have hbθ : 0≤B*θ := mul_nonneg hB hθ.1
    have hc : B*(1-θ)-(n:ℝ)*θ≤-(L:ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc hzi]
  have hlast : (A*Real.exp (B*z.im))^(1-θ)*(E*Real.exp (-(n:ℝ)*z.im))^θ≤
      A*E*Real.exp (-(L:ℝ)*z.im) := by
    rw [Real.mul_rpow (by linarith : 0≤A) (Real.exp_pos _).le,
      Real.mul_rpow (by linarith : 0≤E) (Real.exp_pos _).le,← Real.exp_mul,← Real.exp_mul]
    calc
      _ = (A^(1-θ)*E^θ)*Real.exp (B*z.im*(1-θ)+(-(n:ℝ)*z.im)*θ) := by rw [Real.exp_add]; ring
      _ ≤ (A*E)*Real.exp (-(L:ℝ)*z.im) := by
        apply mul_le_mul
          (mul_le_mul haθ heθ (Real.rpow_nonneg (by linarith) _) (by linarith))
          (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le
          (mul_nonneg (by linarith) (by linarith))
  exact (norm_le_kernel_center F z).trans (hh.trans hlast)
#print axioms exponential_right_propagation
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticExponentialThreeLinesLeftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex Set

/-- The symmetric propagation statement with rapid decay on the left boundary. -/
theorem exponential_left_propagation (F : ℂ → ℂ) (a b C B : ℝ)
    (hab : a<b) (hC : 0≤C) (hB : 0≤B)
    (hF : DiffContOnCl ℂ F (HadamardThreeLines.verticalStrip a b))
    (hg : ∀ z : ℂ,a≤z.re → z.re≤b → ‖F z‖≤C*Real.exp (B*|z.im|))
    (hr : ∀ n : ℕ,∃ D : ℝ,0≤D ∧ ∀ z : ℂ,z.re=a → ‖F z‖≤D*Real.exp (-(n:ℝ)*z.im))
    (u : ℝ) (_hau : a≤u) (hub : u<b) :
    ∀ L : ℕ,∃ K : ℝ,0≤K ∧ ∀ z : ℂ,a≤z.re → z.re≤u → 0≤z.im →
      ‖F z‖≤K*Real.exp (-(L:ℝ)*z.im) := by
  let R : ℝ := |a|+|b|
  have hR : 0≤R := by dsimp [R]; positivity
  have hre (z : ℂ) (hz : a≤z.re ∧ z.re≤b) : |z.re|≤R := by
    apply abs_le.mpr
    dsimp [R]
    constructor <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b,hz.1,hz.2]
  let θ₀ : ℝ := (b-u)/(b-a)
  have hθ₀ : 0<θ₀ := div_pos (sub_pos.mpr hub) (sub_pos.mpr hab)
  obtain ⟨K₀,hK₀,hleft⟩ := kernel_absolute_exponential R B hR hB
  intro L
  obtain ⟨n,hn⟩ := exists_nat_gt ((B+(L:ℝ))/θ₀)
  have hnθ : B+(L:ℝ)<(n:ℝ)*θ₀ := (div_lt_iff₀ hθ₀).mp hn
  obtain ⟨D,hD,hr⟩ := hr n
  obtain ⟨K₁,hK₁,hright⟩ := kernel_signed_exponential R (-(n:ℝ)) hR
  let A : ℝ := K₀*C+1
  let E : ℝ := K₁*D+1
  have hA : 1≤A := by dsimp [A]; nlinarith
  have hE : 1≤E := by dsimp [E]; nlinarith
  refine ⟨A*E,by positivity,?_⟩
  intro z hzl hzb hzi
  let θ : ℝ := (b-z.re)/(b-a)
  have hθ : 0≤θ ∧ θ≤1 := by
    dsimp [θ]
    constructor
    · exact div_nonneg (by linarith) (sub_pos.mpr hab).le
    · apply (div_le_one (sub_pos.mpr hab)).mpr
      linarith
  have hθmin : θ₀≤θ := div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hab).le
  let G : ℂ → ℂ := fun w => kernel z.im w*F w
  have hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip a b) :=
    ⟨(kernel_differentiable z.im).differentiableOn.mul hF.1,
      (kernel_differentiable z.im).continuous.continuousOn.mul hF.2⟩
  have hbound (w : ℂ) (hw : a≤w.re ∧ w.re≤b) :
      ‖G w‖≤A*Real.exp (B*z.im) := by
    dsimp only [G]
    rw [norm_mul]
    have h1 := mul_le_mul_of_nonneg_left (hg w hw.1 hw.2) (norm_nonneg (kernel z.im w))
    have h2 := mul_le_mul_of_nonneg_left (hleft z.im w (hre w hw)) hC
    rw [abs_of_nonneg hzi] at h2
    dsimp [A]
    nlinarith [Real.exp_pos (B*z.im)]
  have hbdd : BddAbove ((norm ∘ G) '' HadamardThreeLines.verticalClosedStrip a b) := by
    refine ⟨A*Real.exp (B*z.im),?_⟩
    rintro v ⟨w,hw,rfl⟩
    exact hbound w hw
  have hright' (w : ℂ) (hw : w.re=a) : ‖G w‖≤E*Real.exp (-(n:ℝ)*z.im) := by
    dsimp only [G]
    rw [norm_mul]
    have h1 := mul_le_mul_of_nonneg_left (hr w hw) (norm_nonneg (kernel z.im w))
    have h2 := mul_le_mul_of_nonneg_left (hright z.im w (hre w ⟨hw.ge,by linarith⟩)) hD
    dsimp [E]
    nlinarith [Real.exp_pos (-(n:ℝ)*z.im)]
  have hh := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab
    (show z∈HadamardThreeLines.verticalClosedStrip a b from ⟨hzl,by linarith⟩) hG hbdd
    (fun w hw => hright' w hw)
    (fun w hw => by change w.re=b at hw; exact hbound w ⟨by linarith,hw.le⟩)
  have hγ : (z.re-a)/(b-a)=1-θ := by
    dsimp [θ]
    field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  rw [hγ,sub_sub_cancel,mul_comm] at hh
  change ‖G z‖≤(A*Real.exp (B*z.im))^(1-θ)*(E*Real.exp (-(n:ℝ)*z.im))^θ at hh
  have haθ : A^(1-θ)≤A := by
    have ht := Real.rpow_le_rpow_of_exponent_le hA (by linarith [hθ.1] : 1-θ≤1)
    simpa only [Real.rpow_one] using ht
  have heθ : E^θ≤E := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hE hθ.2
  have hexponent : B*z.im*(1-θ)+(-(n:ℝ)*z.im)*θ≤-(L:ℝ)*z.im := by
    have hnθ' := mul_le_mul_of_nonneg_left hθmin (Nat.cast_nonneg (α:=ℝ) n)
    have hbθ : 0≤B*θ := mul_nonneg hB hθ.1
    have hc : B*(1-θ)-(n:ℝ)*θ≤-(L:ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc hzi]
  have hlast : (A*Real.exp (B*z.im))^(1-θ)*(E*Real.exp (-(n:ℝ)*z.im))^θ≤
      A*E*Real.exp (-(L:ℝ)*z.im) := by
    rw [Real.mul_rpow (by linarith : 0≤A) (Real.exp_pos _).le,
      Real.mul_rpow (by linarith : 0≤E) (Real.exp_pos _).le,← Real.exp_mul,← Real.exp_mul]
    calc
      _ = (A^(1-θ)*E^θ)*Real.exp (B*z.im*(1-θ)+(-(n:ℝ)*z.im)*θ) := by rw [Real.exp_add]; ring
      _ ≤ (A*E)*Real.exp (-(L:ℝ)*z.im) := by
        apply mul_le_mul
          (mul_le_mul haθ heθ (Real.rpow_nonneg (by linarith) _) (by linarith))
          (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le
          (mul_nonneg (by linarith) (by linarith))
  exact (norm_le_kernel_center F z).trans (hh.trans hlast)
#print axioms exponential_left_propagation
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticGaussianLocalizationBoundsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex

theorem localized_polynomial_bound (R : ℝ) (hR : 0≤R) (n : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ (F : ℂ → ℂ) (C t : ℝ) (z : ℂ),0≤C → |z.re|≤R →
      ‖F z‖≤C*(1+‖z‖)^n → ‖kernel t z*F z‖≤K*C*(1+|t|)^n := by
  obtain ⟨K,hK,h⟩ := kernel_weight_bounds R hR n
  refine ⟨K,hK,?_⟩
  intro F C t z hC hz hF
  rw [norm_mul]
  calc
    ‖kernel t z‖*‖F z‖≤‖kernel t z‖*(C*(1+‖z‖)^n) :=
      mul_le_mul_of_nonneg_left hF (norm_nonneg _)
    _ = C*(‖kernel t z‖*(1+‖z‖)^n) := by ring
    _ ≤ C*(K*(1+|t|)^n) := mul_le_mul_of_nonneg_left (h t z hz).1 hC
    _ = _ := by ring

theorem localized_decay_bound (R : ℝ) (hR : 0≤R) (n : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ (F : ℂ → ℂ) (C t : ℝ) (z : ℂ),0≤C → |z.re|≤R →
      (1+‖z‖)^n*‖F z‖≤C → (1+|t|)^n*‖kernel t z*F z‖≤K*C := by
  obtain ⟨K,hK,h⟩ := kernel_weight_bounds R hR n
  refine ⟨K,hK,?_⟩
  intro F C t z _ hz hF
  rw [norm_mul]
  calc
    (1+|t|)^n*(‖kernel t z‖*‖F z‖)=((1+|t|)^n*‖kernel t z‖)*‖F z‖ := by ring
    _ ≤ (K*(1+‖z‖)^n)*‖F z‖ := mul_le_mul_of_nonneg_right (h t z hz).2 (norm_nonneg _)
    _ = K*((1+‖z‖)^n*‖F z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hF hK
#print axioms localized_polynomial_bound
#print axioms localized_decay_bound
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticThreeLinesMidpointV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex Set

theorem midpoint_square {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b A B : ℝ} (hab : a<b) (hA : 0≤A) (hB : 0≤B)
    (hbounded : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip a b))
    (ha : ∀ z : ℂ,z.re=a → ‖F z‖≤A)
    (hb : ∀ z : ℂ,z.re=b → ‖F z‖≤B)
    {z : ℂ} (hz : z.re=(a+b)/2) : ‖F z‖^2≤A*B := by
  have hmem : z∈Complex.HadamardThreeLines.verticalClosedStrip a b := by
    constructor <;> linarith
  have he : (z.re-a)/(b-a)=(1/2:ℝ) := by
    rw [hz]
    field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  have hh := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hab hmem hF.diffContOnCl hbounded (fun w hw => ha w hw) (fun w hw => hb w hw)
  rw [he,show (1:ℝ)-1/2=1/2 by norm_num,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hh
  calc
    ‖F z‖^2≤(Real.sqrt A*Real.sqrt B)^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = A*B := by rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB]
#print axioms midpoint_square
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidMidpointV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex Set QuantitativeArithmeticVerticalBounded

def RapidLine (F : ℂ → ℂ) (σ : ℝ) : Prop :=
  ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ z : ℂ,z.re=σ → (1+‖z‖)^n*‖F z‖≤C

/-- Polynomial strip growth plus rapid decay on one boundary forces rapid
decay on the midpoint line. Gaussian localization retains the imaginary
height in the three-lines estimate. -/
theorem rapid_midpoint {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℝ} (hab : a<b)
    (hpoly : PolynomialOn {z : ℂ | a≤z.re ∧ z.re≤b} F)
    (hr : RapidLine F b) : RapidLine F ((a+b)/2) := by
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  let R : ℝ := |a|+|b|
  have hR : 0≤R := by dsimp [R]; positivity
  have hre (z : ℂ) (hz : a≤z.re ∧ z.re≤b) : |z.re|≤R := by
    apply abs_le.mpr
    dsimp [R]
    constructor <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b,hz.1,hz.2]
  obtain ⟨K,hK,hloc⟩ := localized_polynomial_bound R hR d
  intro n
  obtain ⟨C',hC',hr⟩ := hr (d+2*n)
  obtain ⟨K',hK',hdec⟩ := localized_decay_bound R hR (d+2*n)
  let P : ℝ := K*C*(K'*C')
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨(1+|(a+b)/2|)^n*Real.sqrt P,by positivity,?_⟩
  intro z hz
  let X : ℝ := 1+|z.im|
  have hX : 0<X := by dsimp [X]; positivity
  let A : ℝ := K*C*X^d
  let B : ℝ := K'*C'/X^(d+2*n)
  let G : ℂ → ℂ := fun w => kernel z.im w*F w
  have hG : Differentiable ℂ G := (kernel_differentiable z.im).mul hF
  have hbound (w : ℂ) (hw : a≤w.re ∧ w.re≤b) : ‖G w‖≤A :=
    hloc F C z.im w hC (hre w hw) (hpoly w hw)
  have hbdd : BddAbove ((norm ∘ G) '' HadamardThreeLines.verticalClosedStrip a b) := by
    refine ⟨A,?_⟩
    rintro y ⟨w,hw,rfl⟩
    exact hbound w hw
  have hsquare : ‖G z‖^2≤A*B := midpoint_square hG hab
    (by dsimp [A]; positivity) (by dsimp [B]; positivity) hbdd
    (fun w hw => hbound w ⟨hw.ge,by linarith⟩)
    (fun w hw => by
      apply (le_div_iff₀ (pow_pos hX _)).mpr
      have hh := hdec F C' z.im w hC' (hre w ⟨by linarith,hw.le⟩) (hr w hw)
      simpa only [X,G,mul_comm] using hh) hz
  have hnorm : ‖F z‖≤‖G z‖ := norm_le_kernel_center F z
  have hs : (X^n*‖F z‖)^2≤P := by
    have hh := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (X^n))
    have he : (X^n)^2*(A*B)=P := by
      dsimp only [A,B,P]
      rw [show X^(d+2*n)=X^d*(X^n)^2 by rw [pow_add,show 2*n=n*2 by omega,pow_mul]]
      field_simp
    rw [he] at hh
    have hn := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hn (sq_nonneg _)).trans hh
  have hsqrt : X^n*‖F z‖≤Real.sqrt P := by
    have hp := Real.sq_sqrt hP
    have hn : 0≤X^n*‖F z‖ := by positivity
    nlinarith [Real.sqrt_nonneg P]
  have hzbound : 1+‖z‖≤(1+|(a+b)/2|)*X := by
    have hh := norm_le_abs_re_add_abs_im z
    rw [hz] at hh
    dsimp [X]
    nlinarith [abs_nonneg z.im,abs_nonneg ((a+b)/2)]
  calc
    (1+‖z‖)^n*‖F z‖≤((1+|(a+b)/2|)*X)^n*‖F z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzbound n) (norm_nonneg _)
    _ = (1+|(a+b)/2|)^n*(X^n*‖F z‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
#print axioms rapid_midpoint
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidAllLinesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open QuantitativeArithmeticVerticalBounded

theorem rapid_all_lines {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpoly : StripPolynomial F) (B : ℝ)
    (hr : ∀ σ : ℝ,B<σ → RapidLine F σ) : ∀ σ : ℝ,RapidLine F σ := by
  intro σ
  let b : ℝ := max σ B+1
  have hσ : σ<b := by dsimp [b]; linarith [le_max_left σ B]
  have hB : B<b := by dsimp [b]; linarith [le_max_right σ B]
  have h := rapid_midpoint hF (by linarith : 2*σ-b<b) (hpoly (2*σ-b) b) (hr b hB)
  have he : ((2*σ-b)+b)/2=σ := by ring
  rwa [he] at h
#print axioms rapid_all_lines
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidLineAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex Set QuantitativeArithmeticVerticalBounded

theorem rapidLine_of_rapid {F : ℂ → ℂ} {σ : ℝ} (h : FinitenessBoundaryDecay.Rapid F σ) :
    RapidLine F σ := by
  intro n
  obtain ⟨A,hA⟩ := h 0
  obtain ⟨B,hB⟩ := h n
  refine ⟨2^(n-1)*(max A 0+max B 0),by positivity,?_⟩
  intro z hz
  have ha : ‖F z‖≤max A 0 := (by simpa using hA z hz : ‖F z‖≤A).trans (le_max_left _ _)
  have hb : ‖z‖^n*‖F z‖≤max B 0 := (hB z hz).trans (le_max_left _ _)
  have hp := add_pow_le (by norm_num : (0:ℝ)≤1) (norm_nonneg z) n
  simp only [one_pow] at hp
  calc
    (1+‖z‖)^n*‖F z‖≤(2^(n-1)*(1+‖z‖^n))*‖F z‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 2^(n-1)*(‖F z‖+‖z‖^n*‖F z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)

theorem RapidLine.toRapid {F : ℂ → ℂ} {σ : ℝ} (h : RapidLine F σ) :
    FinitenessBoundaryDecay.Rapid F σ := by
  intro n
  obtain ⟨C,_,hC⟩ := h n
  exact ⟨C,fun z hz => (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖z‖≤1+‖z‖) n) (norm_nonneg _)).trans (hC z hz)⟩

theorem RapidLine.congr {F G : ℂ → ℂ} {σ : ℝ} (h : RapidLine F σ)
    (he : ∀ z : ℂ,z.re=σ → F z=G z) : RapidLine G σ := by
  intro n
  obtain ⟨C,hC,h⟩ := h n
  exact ⟨C,hC,fun z hz => by rw [← he z hz]; exact h z hz⟩

theorem RapidLine.polynomial_mul {F G : ℂ → ℂ} {σ : ℝ}
    (hF : PolynomialGrowth F) (hG : RapidLine G σ) : RapidLine (fun s => F s*G s) σ := by
  obtain ⟨d,A,hA,hF⟩ := hF
  intro n
  obtain ⟨C,hC,hG⟩ := hG (n+d)
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro s hs
  rw [norm_mul]
  calc
    (1+‖s‖)^n*(‖F s‖*‖G s‖)≤(1+‖s‖)^n*((A*(1+‖s‖)^d)*‖G s‖) := by
      gcongr
      exact hF s
    _ = A*((1+‖s‖)^(n+d)*‖G s‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hG s hs) hA

theorem RapidLine.sum {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (σ : ℝ)
    (hF : ∀ i∈t,RapidLine (F i) σ) : RapidLine (fun s => ∑ i∈t,F i s) σ := by
  classical
  intro n
  have hh (i : t) := hF i.val i.property n
  choose C hC hc using hh
  refine ⟨∑ i : t,C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro s hs
  dsimp only
  rw [← Finset.sum_coe_sort t (fun i => F i s)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hc i s hs)
#print axioms RapidLine.polynomial_mul
#print axioms RapidLine.sum
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidStripV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex Set QuantitativeArithmeticVerticalBounded

theorem bounded_three_lines {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b C : ℝ} (hab : a<b) (hC : 0<C)
    (hbounded : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip a b))
    (ha : ∀ z : ℂ,z.re=a → ‖F z‖≤C)
    (hb : ∀ z : ℂ,z.re=b → ‖F z‖≤C)
    {z : ℂ} (hz : a≤z.re ∧ z.re≤b) : ‖F z‖≤C := by
  have hh := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hab hz hF.diffContOnCl hbounded (fun w hw => ha w hw) (fun w hw => hb w hw)
  rwa [← Real.rpow_add hC,sub_add_cancel,Real.rpow_one] at hh

def RapidStrip (F : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ z : ℂ,a≤z.re → z.re≤b → (1+‖z‖)^n*‖F z‖≤C

theorem rapid_strip {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a b : ℝ} (hab : a<b)
    (hpoly : PolynomialOn {z : ℂ | a≤z.re ∧ z.re≤b} F)
    (ha : RapidLine F a) (hb : RapidLine F b) : RapidStrip F a b := by
  obtain ⟨d,C,hC,hpoly⟩ := hpoly
  let R : ℝ := |a|+|b|
  have hR : 0≤R := by dsimp [R]; positivity
  have hre (z : ℂ) (hz : a≤z.re ∧ z.re≤b) : |z.re|≤R := by
    apply abs_le.mpr
    dsimp [R]
    constructor <;> linarith [neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b,hz.1,hz.2]
  obtain ⟨K,hK,hloc⟩ := localized_polynomial_bound R hR d
  intro n
  obtain ⟨Ca,hCa,ha⟩ := ha n
  obtain ⟨Cb,hCb,hb⟩ := hb n
  obtain ⟨K',hK',hdec⟩ := localized_decay_bound R hR n
  let P : ℝ := K'*(Ca+Cb)+1
  have hP : 0<P := by dsimp [P]; positivity
  refine ⟨(1+R)^n*P,by positivity,?_⟩
  intro z hza hzb
  let X : ℝ := 1+|z.im|
  have hX : 0<X := by dsimp [X]; positivity
  let G : ℂ → ℂ := fun w => kernel z.im w*F w
  have hG : Differentiable ℂ G := (kernel_differentiable z.im).mul hF
  have hbound (w : ℂ) (hw : a≤w.re ∧ w.re≤b) : ‖G w‖≤K*C*X^d :=
    hloc F C z.im w hC (hre w hw) (hpoly w hw)
  have hbdd : BddAbove ((norm ∘ G) '' HadamardThreeLines.verticalClosedStrip a b) := by
    refine ⟨K*C*X^d,?_⟩
    rintro y ⟨w,hw,rfl⟩
    exact hbound w hw
  have hleft (w : ℂ) (hw : w.re=a) : ‖G w‖≤P/X^n := by
    apply (le_div_iff₀ (pow_pos hX _)).mpr
    have hh := hdec F Ca z.im w hCa (hre w ⟨hw.ge,by linarith⟩) (ha w hw)
    change X^n*‖G w‖≤K'*Ca at hh
    dsimp only [P]
    nlinarith
  have hright (w : ℂ) (hw : w.re=b) : ‖G w‖≤P/X^n := by
    apply (le_div_iff₀ (pow_pos hX _)).mpr
    have hh := hdec F Cb z.im w hCb (hre w ⟨by linarith,hw.le⟩) (hb w hw)
    change X^n*‖G w‖≤K'*Cb at hh
    dsimp only [P]
    nlinarith
  have hgz := bounded_three_lines hG hab (div_pos hP (pow_pos hX _)) hbdd hleft hright ⟨hza,hzb⟩
  have hnorm : ‖F z‖≤‖G z‖ := norm_le_kernel_center F z
  have hw : X^n*‖F z‖≤P := by
    have hh := (le_div_iff₀ (pow_pos hX _)).mp (hnorm.trans hgz)
    nlinarith
  have hzbound : 1+‖z‖≤(1+R)*X := by
    have hh := norm_le_abs_re_add_abs_im z
    have hh' := hre z ⟨hza,hzb⟩
    dsimp [X]
    nlinarith [abs_nonneg z.im]
  calc
    (1+‖z‖)^n*‖F z‖≤((1+R)*X)^n*‖F z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzbound n) (norm_nonneg _)
    _ = (1+R)^n*(X^n*‖F z‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
#print axioms rapid_strip
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidVerticalIntegrableV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex MeasureTheory

theorem RapidLine.cauchy_bound {F : ℂ → ℂ} {σ : ℝ} (h : RapidLine F σ) :
    ∃ C : ℝ,0≤C ∧ ∀ z : ℂ,z.re=σ → ‖F z‖≤C/(1+z.im^2) := by
  obtain ⟨C,hC,h⟩ := h 2
  refine ⟨C,hC,?_⟩
  intro z hz
  apply (le_div_iff₀ (by positivity : 0<1+z.im^2)).mpr
  have hi := abs_im_le_norm z
  have hn : 1+z.im^2≤(1+‖z‖)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg z.im) hi 2
    rw [sq_abs] at hh
    nlinarith [norm_nonneg z]
  have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg (F z))
  have hb := h z hz
  nlinarith

theorem RapidLine.vertical_integrable {F : ℂ → ℂ} {σ : ℝ} (h : RapidLine F σ)
    (hc : Continuous (fun t : ℝ => F ((σ:ℂ)+(t:ℂ)*I))) : VerticalIntegrable F σ := by
  obtain ⟨C,_,hC⟩ := h.cauchy_bound
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have hh := hC ((σ:ℂ)+(t:ℂ)*I) (by simp)
  simpa only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add,div_eq_mul_inv] using hh

theorem RapidLine.of_norm_le {F G : ℂ → ℂ} {σ C : ℝ} (hF : RapidLine F σ)
    (hC : 0≤C) (hG : ∀ z : ℂ,z.re=σ → ‖G z‖≤C*‖F z‖) : RapidLine G σ := by
  intro n
  obtain ⟨A,hA,ha⟩ := hF n
  refine ⟨C*A,mul_nonneg hC hA,?_⟩
  intro z hz
  calc
    (1+‖z‖)^n*‖G z‖≤(1+‖z‖)^n*(C*‖F z‖) :=
      mul_le_mul_of_nonneg_left (hG z hz) (by positivity)
    _ = C*((1+‖z‖)^n*‖F z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ha z hz) hC
#print axioms RapidLine.vertical_integrable
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidQuotientV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex QuantitativeArithmeticVerticalBounded

theorem RapidStrip.line {F : ℂ → ℂ} {a b σ : ℝ} (h : RapidStrip F a b)
    (ha : a≤σ) (hb : σ≤b) : RapidLine F σ := by
  intro n
  obtain ⟨C,hC,h⟩ := h n
  exact ⟨C,hC,fun z hz => h z (by linarith) (by linarith)⟩

theorem RapidStrip.cauchy_bound {F : ℂ → ℂ} {a b : ℝ} (h : RapidStrip F a b) :
    ∃ C : ℝ,0≤C ∧ ∀ z : ℂ,a≤z.re → z.re≤b → ‖F z‖≤C/(1+z.im^2) := by
  obtain ⟨C,hC,h⟩ := h 2
  refine ⟨C,hC,?_⟩
  intro z ha hb
  apply (le_div_iff₀ (by positivity : 0<1+z.im^2)).mpr
  have hi := pow_le_pow_left₀ (abs_nonneg z.im) (abs_im_le_norm z) 2
  rw [sq_abs] at hi
  have hn : 1+z.im^2≤(1+‖z‖)^2 := by nlinarith [norm_nonneg z]
  have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg (F z))
  have hh' := h z ha hb
  nlinarith

theorem RapidStrip.bounded_mul {F G : ℂ → ℂ} {a b : ℝ} (hf : RapidStrip F a b)
    (hg : Bounded G) : RapidStrip (fun z => G z*F z) a b := by
  obtain ⟨A,hA,hg⟩ := hg a b
  intro n
  obtain ⟨C,hC,hf⟩ := hf n
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro z ha hb
  rw [norm_mul]
  calc
    (1+‖z‖)^n*(‖G z‖*‖F z‖)≤(1+‖z‖)^n*(A*‖F z‖) := by
      gcongr
      exact hg z ha hb
    _ = A*((1+‖z‖)^n*‖F z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf z ha hb) hA

theorem RapidLine.div_real_shift {H : ℂ → ℂ} {σ : ℝ} (hH : RapidLine H σ)
    (k : ℝ) (hσ : σ≠k) : RapidLine (fun z => H z/(z-(k:ℂ))) σ := by
  apply hH.of_norm_le (inv_nonneg.mpr (abs_nonneg (σ-k)))
  intro z hz
  have hnorm : |σ-k|≤‖z-(k:ℂ)‖ := by
    have h := abs_re_le_norm (z-(k:ℂ))
    simpa only [sub_re,ofReal_re,hz] using h
  have hi := inv_anti₀ (abs_pos.mpr (sub_ne_zero.mpr hσ)) hnorm
  rw [norm_div,div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (norm_nonneg (H z))

theorem quotient_vertical_integrable {H : ℂ → ℂ} (hH : Continuous H)
    {σ : ℝ} (hr : RapidLine H σ) (k : ℝ) (hσ : σ≠k) :
    VerticalIntegrable (fun z => H z/(z-(k:ℂ))) σ := by
  apply (hr.div_real_shift k hσ).vertical_integrable
  apply Continuous.div (hH.comp (by fun_prop)) (by fun_prop)
  intro t ht
  apply hσ
  have hh := congrArg Complex.re (sub_eq_zero.mp ht)
  simpa using hh

theorem quotient_tail_bound (H : ℂ → ℂ) (k a b C : ℝ)
    (h : ∀ z : ℂ,a≤z.re → z.re≤b → ‖H z‖≤C/(1+z.im^2)) :
    ∀ z : ℂ,a≤z.re → z.re≤b → 1≤|z.im| →
      ‖H z/(z-(k:ℂ))‖≤C/(1+z.im^2) := by
  intro z ha hb hi
  have hn : 1≤‖z-(k:ℂ)‖ := by
    have hh := abs_im_le_norm (z-(k:ℂ))
    simp only [sub_im,ofReal_im,sub_zero] at hh
    exact hi.trans hh
  rw [norm_div]
  exact (div_le_self (norm_nonneg _) hn).trans (h z ha hb)

theorem entire_quotient_regular_part (H : ℂ → ℂ) (hH : Differentiable ℂ H) (k : ℂ) :
    ∃ E : ℂ → ℂ,Differentiable ℂ E ∧
      ∀ z : ℂ,z≠k → E z=H z/(z-k)-H k/(z-k) := by
  refine ⟨dslope H k,?_,?_⟩
  · intro z
    by_cases hz : z=k
    · subst z
      obtain ⟨p,hp⟩ := hH.analyticAt k
      exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
    · exact (differentiableAt_dslope_of_ne hz).mpr (hH z)
  · intro z hz
    rw [dslope_of_ne H hz,slope,smul_eq_mul]
    simp only [vsub_eq_sub]
    ring
#print axioms quotient_vertical_integrable
#print axioms entire_quotient_regular_part
end QuantitativeArithmeticGaussianStrip
end
end

/-! ## QuantitativeArithmeticRapidQuotientContourV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticGaussianStrip
open Complex MeasureTheory QuantitativeArithmeticVerticalBounded

theorem rapid_quotient_contour (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (k a b : ℝ) (ha : a<k) (hb : k<b) (hr : RapidStrip H a b) :
    (∫ t : ℝ,H ((b:ℂ)+(t:ℂ)*I)/((b:ℂ)+(t:ℂ)*I-(k:ℂ)))=
      (∫ t : ℝ,H ((a:ℂ)+(t:ℂ)*I)/((a:ℂ)+(t:ℂ)*I-(k:ℂ)))+2*(Real.pi:ℂ)*H (k:ℂ) := by
  obtain ⟨E,hE,he⟩ := entire_quotient_regular_part H hH (k:ℂ)
  obtain ⟨C,_,hC⟩ := hr.cauchy_bound
  exact QuantitativeArithmeticSimplePoleContour.vertical_difference
    (fun z => H z/(z-(k:ℂ))) E (H (k:ℂ)) k a b C ha hb hE he
    (quotient_tail_bound H k a b C hC)
    (quotient_vertical_integrable hH.continuous (hr.line le_rfl (ha.trans hb).le) k (ne_of_lt ha))
    (quotient_vertical_integrable hH.continuous (hr.line (ha.trans hb).le le_rfl) k (ne_of_gt hb))

theorem rapid_quotient_mellin_shift (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (k a b : ℝ) (ha : a<k) (hb : k<b) (hr : RapidStrip H a b)
    (y : ℝ) (hy : 0<y) :
    mellinInv b (fun z => H z/(z-(k:ℂ))) y=
      mellinInv a (fun z => H z/(z-(k:ℂ))) y+(y:ℂ)^(-(k:ℂ))*H (k:ℂ) := by
  let J : ℂ → ℂ := fun z => exp (((-Real.log y:ℝ):ℂ)*z)*H z
  have hJ : Differentiable ℂ J := by
    apply Differentiable.mul _ hH
    fun_prop
  have hexp : Bounded (fun z : ℂ => exp (((-Real.log y:ℝ):ℂ)*z)) := by
    simpa only [Complex.ofReal_zero,sub_zero] using exponential (-Real.log y) 0
  have hJr : RapidStrip J a b := hr.bounded_mul hexp
  have hshift := rapid_quotient_contour J hJ k a b ha hb hJr
  let Q : ℂ → ℂ := fun z => H z/(z-(k:ℂ))
  have hfun : FinitenessMellinContour.kernel Q (Real.log y)=(fun z => J z/(z-(k:ℂ))) := by
    funext z
    dsimp [FinitenessMellinContour.kernel,Q,J]
    ring
  have hk : J (k:ℂ)=(y:ℂ)^(-(k:ℂ))*H (k:ℂ) := by
    have hh := FinitenessMellinContour.kernel_log hy (fun _ => (1:ℂ)) (k:ℂ)
    simp only [FinitenessMellinContour.kernel,mul_one] at hh
    exact congrArg (fun v => v*H (k:ℂ)) hh
  change mellinInv b Q y=mellinInv a Q y+_
  rw [FinitenessMellinContour.mellinInv_eq hy,FinitenessMellinContour.mellinInv_eq hy]
  simp only [FinitenessMellinContour.integral,hfun]
  rw [hshift,smul_add]
  congr 1
  rw [Complex.real_smul,hk]
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
#print axioms rapid_quotient_mellin_shift
end QuantitativeArithmeticGaussianStrip
end
end
