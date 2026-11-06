module

public import SmallLevelTwentyOneWordCertificateV1
public import SmallLevelTwentyOneTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne SmallLevelTaylor

def primeParameter (p m : ℕ) (s : ℂ) : ℂ := (p:ℂ)^(s-(m:ℂ))

def threePrimeMonomial (e : ℤ×ℤ×ℤ) (x y z : ℂ) : ℂ := x^e.1*y^e.2.1*z^e.2.2

theorem positive_zpow_cpow_direct {p : ℝ} (hp : 0<p) (e : ℤ) (s : ℂ) :
    ((p:ℂ)^e)^s=((p:ℂ)^s)^e := by
  rw [SmallLevelTwentyOne.positive_zpow_cpow hp,Complex.cpow_neg,inv_zpow,← zpow_neg,neg_neg]

theorem rational_three_prime_power (r : ℚ) (e : ℤ×ℤ×ℤ)
    (hr : r=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(7:ℚ)^e.2.2) (s : ℂ) :
    (r:ℂ)^s=threePrimeMonomial e ((2:ℂ)^s) ((3:ℂ)^s) ((7:ℂ)^s) := by
  have hreal : (r:ℝ)=(2:ℝ)^e.1*(3:ℝ)^e.2.1*(7:ℝ)^e.2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℝ)) hr
  have hc : (r:ℂ)=(((2:ℝ)^e.1*(3:ℝ)^e.2.1*(7:ℝ)^e.2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun t : ℝ => (t:ℂ)) hreal
  rw [hc,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow_direct (by norm_num : (0:ℝ)<2),
    positive_zpow_cpow_direct (by norm_num : (0:ℝ)<3),
    positive_zpow_cpow_direct (by norm_num : (0:ℝ)<7)]
  rfl

theorem primeParameter_shift (p m : ℕ) (hp : p≠0) (s : ℂ) :
    primeParameter p m (s-1)=primeParameter p m s/(p:ℂ) := by
  unfold primeParameter
  rw [show s-1-(m:ℂ)=(s-(m:ℂ))-1 by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one]

theorem certificate_leading_laurent (r : WordCertificate) (m : ℕ) (χ s : ℂ) :
    certificateCoefficient r m χ 0 s=χ^r.count*threePrimeMonomial r.powers
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) := by
  simp only [certificateCoefficient,pow_zero,Ring.choose_zero_right,mul_one]
  rw [rational_three_prime_power _ _ r.powers_eq]
  rfl

theorem certificate_first_shift_factor (r : WordCertificate) (m : ℕ) (χ s : ℂ) :
    certificateCoefficient r m χ 1 (s-1)=I*(s-((2*m:ℕ):ℂ))*
      certificateCoefficient r m χ 0 (s-1)*(r.slope:ℂ) := by
  simp only [certificateCoefficient,pow_one,pow_zero,Ring.choose_one_right,
    Ring.choose_zero_right,mul_one,Nat.cast_one,Nat.cast_zero,add_zero]
  ring

theorem certificate_first_shift_laurent (r : WordCertificate) (m : ℕ) (χ s : ℂ) :
    certificateCoefficient r m χ 1 (s-1)=I*(s-((2*m:ℕ):ℂ))*χ^r.count*
      threePrimeMonomial r.powers (primeParameter 2 m s/2)
        (primeParameter 3 m s/3) (primeParameter 7 m s/7)*(r.slope:ℂ) := by
  rw [certificate_first_shift_factor,certificate_leading_laurent,
    primeParameter_shift 2 m (by decide),primeParameter_shift 3 m (by decide),
    primeParameter_shift 7 m (by decide)]
  norm_num only [Nat.cast_ofNat]
  ring

def ramanujanRate (q : ℕ) (t : ℤ) : ℚ := (Nat.lcm 21 (q^2):ℚ)*((t:ℚ)/42)^2

def ramanujanSlope (q : ℕ) (t : ℤ) : ℚ := (Nat.lcm 21 (q^2):ℚ)*(t:ℚ)/42

theorem fullTaylorCoefficient_rational (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    {q : ℕ} (hq : q∣42) (t : ℤ) (n : ℕ) (s : ℂ) :
    fullTaylorCoefficient (2*m) f ε q t n s=
      phaseRoot m ε*localRoot (rootU f) (rootV f) q*(ramanujanRate q t:ℂ)^(s-(m:ℂ))*
        (I*(ramanujanSlope q t:ℂ))^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hr : (((Nat.lcm 21 (q^2):ℝ)*((t:ℝ)/42)^2:ℝ):ℂ)=(ramanujanRate q t:ℂ) := by
    simp [ramanujanRate]
  have hd : I*(Nat.lcm 21 (q^2):ℂ)*(((t:ℝ)/42:ℝ):ℂ)=I*(ramanujanSlope q t:ℂ) := by
    simp [ramanujanSlope]
    ring
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  unfold fullTaylorCoefficient taylorRowScalar
  rw [root_grid_divisor f hq,hr]
  simp only [Complex.ofReal_natCast]
  rw [hd,hm]
  unfold phaseRoot
  ring

#print axioms rational_three_prime_power
#print axioms certificate_leading_laurent
#print axioms certificate_first_shift_laurent
#print axioms fullTaylorCoefficient_rational
end SmallLevelTwentyOneKnownWords
