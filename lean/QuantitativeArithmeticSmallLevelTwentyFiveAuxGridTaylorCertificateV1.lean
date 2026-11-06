module

public import QuantitativeArithmeticSmallLevelTwentyFiveFiniteGridTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveGridSystemTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
open Complex QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid QuantitativeArithmeticSmallLevelTwentyFiveKnownWords SmallLevelTaylor Set
open QuantitativeArithmeticSmallLevelTwentyFive
open QuantitativeArithmeticSmallLevelTwentyFive.GridSystem (phaseRoot)

def taylorRate (q : ℕ) (t : ℤ) : ℚ := (Nat.lcm 25 (q^2):ℚ)*((t:ℚ)/1050)^2
def taylorSlope (q : ℕ) (t : ℤ) : ℚ := (Nat.lcm 25 (q^2):ℚ)*(t:ℚ)/1050

structure TaylorCertificate where
  q : ℕ
  source : ℤ
  target : ℤ
  d : ℤ
  positive : 0<q
  divides : q∣1050
  nonzero : source≠0
  level_identity : (Nat.lcm 25 (q^2):ℤ)*d=(1050:ℤ)^2
  source_divides : source∣d
  target_eq : target= -(d/source)
  rate : ℚ
  slope : ℚ
  powers : ℤ×ℤ×ℤ×ℤ
  rate_eq : taylorRate q source=rate
  slope_eq : taylorSlope q source=slope
  powers_eq : rate=(2:ℚ)^powers.1*(3:ℚ)^powers.2.1*(5:ℚ)^powers.2.2.1*(7:ℚ)^powers.2.2.2

theorem taylorCoefficient_rational (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    {q : ℕ} (_hq : q∣1050) (t : ℤ) (n : ℕ) (s : ℂ) :
    taylorCoefficient 1050 (2*m) f ε q t n s=
      phaseRoot m ε*(taylorRate q t:ℂ)^(s-(m:ℂ))*
        (I*(taylorSlope q t:ℂ))^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hr : (((Nat.lcm 25 (q^2):ℝ)*((t:ℝ)/1050)^2:ℝ):ℂ)=(taylorRate q t:ℂ) := by
    simp [taylorRate]
  have hd : I*(Nat.lcm 25 (q^2):ℂ)*(((t:ℝ)/1050:ℝ):ℂ)=I*(taylorSlope q t:ℂ) := by
    simp [taylorSlope]
    ring
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  unfold taylorCoefficient taylorRowScalar
  rw [twist_root_one,one_mul]
  simp only [Nat.cast_ofNat,Complex.ofReal_natCast]
  rw [hr]
  rw [hd,hm]
  unfold phaseRoot
  ring

theorem taylor_certificate_leading (r : TaylorCertificate) (m : ℕ) (f : ℕ → ℂ)
    (ε s : ℂ) :
    taylorCoefficient 1050 (2*m) f ε r.q r.source 0 s=
      phaseRoot m ε*
        fourPrimeMonomial r.powers (primeParameter 2 m s) (primeParameter 3 m s)
          (primeParameter 5 m s) (primeParameter 7 m s) := by
  rw [taylorCoefficient_rational m f ε r.divides]
  simp only [pow_zero,Ring.choose_zero_right,mul_one,r.rate_eq]
  rw [rational_four_prime_power _ _ r.powers_eq]
  rfl

theorem taylor_coefficient_analytic (r : TaylorCertificate) (k : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (taylorCoefficient 1050 k f ε r.q r.source n) s := by
  apply taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<25) (pow_pos r.positive 2)
  · exact div_ne_zero (by exact_mod_cast r.nonzero) (by norm_num)

theorem taylor_certificate_rows (r : TaylorCertificate) {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (taylorError 1050 (2*m) f ε r.q r.source M)
        {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.sampleSum 1050 (by decide) r.q r.source
            (QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.gridVector 1050 (2*m) f s)-
          taylorCoefficient 1050 (2*m) f ε r.q r.source 0 s*
            QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.sampleSum 1050 (by decide) r.q r.target
              (QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.gridVector 1050 (2*m) f s)=
        taylorError 1050 (2*m) f ε r.q r.source M s+∑ n∈Finset.range M,
          taylorCoefficient 1050 (2*m) f ε r.q r.source (n+1) s*
            QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.sampleSum 1050 (by decide) r.q r.target
              (QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.gridVector 1050 (2*m) f (s+((n:ℂ)+1))) := by
  rw [r.target_eq]
  exact original_taylor_rows 1050 (by decide) hf ε hlaw r.q r.positive r.divides
    r.source r.d r.nonzero r.level_identity r.source_divides

#print axioms taylor_certificate_leading
#print axioms taylor_coefficient_analytic
#print axioms taylor_certificate_rows
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
