module

public import QuantitativeArithmeticMaassSourceColumnEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The resolved identity bound is uniform for an enlarged window of at
most twice the original width. The original width remains in the bound. -/
theorem enlargedWindowIdentity_bound (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ C : ℝ,0<C ∧ ∀ (R t ε a b : ℝ) (hR : 1≤R),
      1≤t → 0≤ε → ε≤1 → 1/R≤ε → 0<a → a≤b → b≤2*t → b-a≤2*ε →
      ‖windowIdentityContribution K hc R (lt_of_lt_of_le zero_lt_one hR) a b‖≤C*t*ε := by
  let m₁ := ∫ x,|x| * K x
  let m₂ := ∫ x,|x|^2*K x
  have h₁ : 0≤m₁ := integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (hK x))
  have h₂ : 0≤m₂ := integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hK x))
  refine ⟨(12+24*m₁+8*m₂)/(4*Real.pi),by positivity,?_⟩
  intro R t ε a b hR ht hε hε1 hresolve ha hab hbt hwidth
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  let I := windowIdentityContribution K hc R hRp a b
  have hb := windowIdentityContribution_error K he hc hK hm R hRp a b ha hab
  have hn := norm_le_norm_sub_add ((4*Real.pi:ℂ)*I) (((b^2-a^2:ℝ):ℂ))
  have hcoef : ‖(4*Real.pi:ℂ)‖=4*Real.pi := by
    rw [←Complex.ofReal_ofNat,←Complex.ofReal_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hmain : ‖((b^2-a^2:ℝ):ℂ)‖=b^2-a^2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by nlinarith)]
  rw [norm_mul,hcoef,hmain] at hn
  have hsq : b^2-a^2≤8*t*ε := by
    calc
      _=(b-a)*(b+a) := by ring
      _≤(2*ε)*(4*t) := mul_le_mul hwidth (by linarith) (by linarith) (by positivity)
      _=_ := by ring
  have hfirst : 8*(1+b)*m₁/R≤24*m₁*t*ε := by
    calc
      _=(8*(1+b)*m₁)*(1/R) := by ring
      _≤(8*(1+b)*m₁)*ε := mul_le_mul_of_nonneg_left hresolve (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) h₁)
      _≤_ := by nlinarith [mul_nonneg h₁ hε]
  have hinv : 1/R≤1 := (div_le_one hRp).mpr hR
  have hsecond : 8*m₂/R^2≤8*m₂*t*ε := by
    have hsq' : (1/R)^2≤ε := by
      have hnon : 0≤1/R := by positivity
      nlinarith
    calc
      _=8*m₂*(1/R)^2 := by ring
      _≤8*m₂*ε := mul_le_mul_of_nonneg_left hsq' (by positivity)
      _≤_ := by nlinarith [mul_nonneg h₂ hε]
  have htotal : (4*Real.pi)*‖I‖≤(12+24*m₁+8*m₂)*t*ε := by
    change ‖(4*Real.pi:ℂ)*I-((b^2-a^2:ℝ):ℂ)‖≤
      8*(1+b)*m₁/R+8*m₂/R^2+2*(b-a) at hb
    nlinarith [mul_le_mul_of_nonneg_right ht hε]
  apply (le_div_iff₀ (show 0<4*Real.pi by positivity)).mpr
    (show ‖I‖*(4*Real.pi)≤(12+24*m₁+8*m₂)*t*ε by nlinarith) |>.trans_eq ?_
  ring

/-- The off-diagonal Abel estimate is uniform over the same enlargement. -/
theorem enlargedWindowSquare_abel_decay (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ C : ℝ,0<C ∧ ∀ (R t ε a b d : ℝ) (hR : 1≤R),
      3≤t → 0≤ε → ε≤1 → t-ε≤a → a≤b → b≤2*t → b-a≤2*ε → 0<d →
      ‖abelProfile (evenCoshLift (timeConvolution
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) a b)
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) a b)))
        (Real.cosh d)‖≤C*Real.sqrt t*R^2*ε^2/Real.sqrt (Real.sinh d) := by
  obtain ⟨C,hC,hbound⟩ := windowTimeSquare_abel_decay K he hc
  refine ⟨2*C,by positivity,?_⟩
  intro R t ε a b d hR ht hε hε1 hat hab hbt hwidth hd
  have hh := hbound R ((b-a)/2) ((a+b)/2) d hR (by linarith) (by linarith) (by linarith) hd
  simp only [show (a+b)/2-(b-a)/2=a by ring,
    show (a+b)/2+(b-a)/2=b by ring] at hh
  have hsqrt : Real.sqrt ((a+b)/2)≤2*Real.sqrt t := by
    calc
      _≤Real.sqrt (4*t) := Real.sqrt_le_sqrt (by linarith)
      _=_ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  apply hh.trans
  calc
    _≤C*(2*Real.sqrt t)*R^2*ε^2/Real.sqrt (Real.sinh d) := by gcongr; linarith
    _=_ := by ring

#print axioms enlargedWindowIdentity_bound
#print axioms enlargedWindowSquare_abel_decay
end QuantitativeMaass
