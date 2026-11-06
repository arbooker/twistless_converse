module

public import SmallLevelTwentyOneIntegerWordRatesV1
public import SmallLevelTwentyOneWordInfinityGermsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Filter Set SmallLevelAdditive SmallLevelTaylor
open SmallLevelTwentyOne
open scoped Topology

def rationalWordCoefficient (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (n : ℕ) (s : ℂ) : ℂ :=
  χ^(frickeCount w)*(rationalRate w t : ℂ)^(s-(m:ℂ))*
    (I*(rationalDerivative w t : ℂ))^n*
      Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- Every matrix condition needed to insert this actual continued Taylor
row into the finite pole system is an exact integer calculation. -/
theorem integer_word_grid_germs {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (w : Word) (hC : integerRaw w 1 0≠0) (t u : ℤ)
    (ht : integerDen w t≠0) (hu : 42*integerNumer w t=u*integerDen w t) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ x : ℂ, B-((M:ℝ)+1)<x.re →
        (fun s => G s (gridIndex t)-
          rationalWordCoefficient m (ε*I^(2*m)) w t 0 s*G s (gridIndex u)) =ᶠ[𝓝[≠] x]
        (fun s => error M s+∑ n∈Finset.range M,
          rationalWordCoefficient m (ε*I^(2*m)) w t (n+1) s*
            G (s+((n:ℂ)+1)) (gridIndex u)) := by
  simpa only [wordCoefficient_rational,rationalWordCoefficient] using
    word_grid_germs_of_law hf ε hε hlaw BG G hG hGF w
      ((word_C_integer w).mpr hC) t u ((word_den_integer w t).mpr ht)
      (word_partner_integer w t u ht hu)

/-- Likewise a source-to-infinity row is certified by one zero integer
denominator. Its actual additive Mellin transform is entire. -/
theorem integer_word_infinity_germ {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (w : Word) (hC : integerRaw w 1 0≠0) (t : ℤ) (ht : integerDen w t=0) :
    (∀ x : ℂ, AnalyticAt ℂ (sourceEntire (2*m) f t) x) ∧
      ∀ x : ℂ, (fun s => G s (gridIndex t)) =ᶠ[𝓝[≠] x] sourceEntire (2*m) f t := by
  apply original_word_infinity_germ hm hf BG G hG hGF w ((word_C_integer w).mpr hC) t
  by_contra hn
  exact (word_den_integer w t).mp hn ht

#print axioms integer_word_grid_germs
#print axioms integer_word_infinity_germ
end SmallLevelTwentyOneKnownWords
