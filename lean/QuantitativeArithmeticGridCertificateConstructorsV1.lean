module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridTaylorCertificateV1

set_option autoImplicit false
@[expose] public noncomputable section

/-! Compact exact data constructors for the two types of Taylor row.
Only the numerical data are supplied at each use; a single decidable
conjunction certifies all the fields of the original structure. -/

namespace QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticSmallLevelTwentyFiveKnownWords

def WordCertificate.ofValues (Q : ℕ) (word : Word) (source target : ℤ)
    (rate slope : ℚ) (count : ℕ) (powers : ℤ × ℤ × ℤ × ℤ)
    (h : integerRaw word 1 0 ≠ 0 ∧ integerDen Q word source ≠ 0 ∧
      (Q : ℤ) * integerNumer Q word source = target * integerDen Q word source ∧
      rationalRate Q word source = rate ∧ rationalDerivative Q word source = slope ∧
      frickeCount word = count ∧
      rate = (2 : ℚ)^powers.1 * (3 : ℚ)^powers.2.1 *
        (5 : ℚ)^powers.2.2.1 * (7 : ℚ)^powers.2.2.2) : WordCertificate Q where
  word := word
  source := source
  target := target
  rate := rate
  slope := slope
  count := count
  powers := powers
  nonaffine := h.1
  denominator := h.2.1
  closed := h.2.2.1
  rate_eq := h.2.2.2.1
  slope_eq := h.2.2.2.2.1
  count_eq := h.2.2.2.2.2.1
  powers_eq := h.2.2.2.2.2.2

end QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData

def TaylorCertificate.ofValues (q : ℕ) (source target d : ℤ)
    (rate slope : ℚ) (powers : ℤ × ℤ × ℤ × ℤ)
    (h : 0 < q ∧ q ∣ 1050 ∧ source ≠ 0 ∧
      (Nat.lcm 25 (q^2) : ℤ) * d = (1050 : ℤ)^2 ∧
      source ∣ d ∧ target = -(d/source) ∧ taylorRate q source = rate ∧
      taylorSlope q source = slope ∧
      rate = (2 : ℚ)^powers.1 * (3 : ℚ)^powers.2.1 *
        (5 : ℚ)^powers.2.2.1 * (7 : ℚ)^powers.2.2.2) : TaylorCertificate where
  q := q
  source := source
  target := target
  d := d
  rate := rate
  slope := slope
  powers := powers
  positive := h.1
  divides := h.2.1
  nonzero := h.2.2.1
  level_identity := h.2.2.2.1
  source_divides := h.2.2.2.2.1
  target_eq := h.2.2.2.2.2.1
  rate_eq := h.2.2.2.2.2.2.1
  slope_eq := h.2.2.2.2.2.2.2.1
  powers_eq := h.2.2.2.2.2.2.2.2

end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
