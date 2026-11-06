module

public import SmallLevelTwentyOneWordRowMatrixV1
public import SmallLevelTwentyOnePoleWordRowsV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- Exact finite data for an augmented word row. Every computed field is
linked to the actual integer word by a kernel-checked equality. -/
structure WordCertificate where
  row : ClosedWordRow
  rate : ℚ
  slope : ℚ
  count : ℕ
  powers : ℤ × ℤ × ℤ
  rate_eq : rationalRate row.word row.source = rate
  slope_eq : rationalDerivative row.word row.source = slope
  count_eq : frickeCount row.word = count
  powers_eq : rate = (2:ℚ)^powers.1*(3:ℚ)^powers.2.1*(7:ℚ)^powers.2.2

structure InfinityCertificate where
  word : Word
  source : ℤ
  nonaffine : integerRaw word 1 0 ≠ 0
  denominator : integerDen word source = 0

def certificateCoefficient (r : WordCertificate) (m : ℕ) (χ : ℂ)
    (n : ℕ) (s : ℂ) : ℂ :=
  χ^r.count*(r.rate:ℂ)^(s-(m:ℂ))*(I*(r.slope:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

theorem certificateCoefficient_eq (r : WordCertificate) (m : ℕ) (χ : ℂ)
    (n : ℕ) (s : ℂ) :
    rationalWordCoefficient m χ r.row.word r.row.source n s=
      certificateCoefficient r m χ n s := by
  simp only [rationalWordCoefficient,certificateCoefficient,r.rate_eq,r.slope_eq,r.count_eq]

/-- The exact exported rational row constrains the same actual principal
vector; its rate, slope and sign count are not unproved algebraic inputs. -/
theorem pole_certificate {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (r : WordCertificate) :
    v (gridIndex r.row.source)-certificateCoefficient r m (ε*I^(2*m)) 0 x*
      v (gridIndex r.row.target)=0 := by
  have h := pole_word_constraint hf ε hε hlaw BG G hG hGF x v hv hshift r.row.word
    ((word_C_integer _).mpr r.row.nonaffine) r.row.source r.row.target
    ((word_den_integer _ _).mpr r.row.denominator)
    (word_partner_integer _ _ _ r.row.denominator r.row.closed)
  rw [wordCoefficient_rational] at h
  change v (gridIndex r.row.source)-
    rationalWordCoefficient m (ε*I^(2*m)) r.row.word r.row.source 0 x*
      v (gridIndex r.row.target)=0 at h
  rwa [certificateCoefficient_eq] at h

theorem pole_infinity_certificate {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (r : InfinityCertificate) : v (gridIndex r.source)=0 := by
  apply pole_infinity_constraint hm hf BG G hG hGF x v hv r.word
    ((word_C_integer _).mpr r.nonaffine) r.source
  by_contra hn
  exact (word_den_integer _ _).mp hn r.denominator

#print axioms certificateCoefficient_eq
#print axioms pole_certificate
#print axioms pole_infinity_certificate
end SmallLevelTwentyOneKnownWords
