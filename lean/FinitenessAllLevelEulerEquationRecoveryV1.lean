module

public import FinitenessAllLevelEulerEquationsV1
public import AsymptoticClassicalEulerProductV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelEulerEquations

open FinitenessAllLevelCoefficientFunctional FinitenessAllLevelDiskAlgebra
  FinitenessOriginalInput Filter Asymptotics

variable {R : ℝ}

/-- With an individual polynomial growth bound, the coefficient equations
are equivalent to the literal infinite Euler product, bad-prime conditions
and chosen eigenvalue. Growth is displayed explicitly, not inferred from
membership in a Banach disk algebra. -/
theorem equations_iff_eulerData (N k p : ℕ) (hR : 0 < R) (z : ℂ) (F : space R)
    (hg : ∃ σ : ℝ, 0 < σ ∧ (fun n => normalizedCLM hR k n F) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ)) :
    (∀ e : Equation N, equation N k p hR e (z, F) = 0) ↔
      EulerData N (fun n => normalizedCLM hR k n F) ∧ normalizedCLM hR k p F = z := by
  let f : ℕ → ℂ := fun n => normalizedCLM hR k n F
  constructor
  · intro he
    have h0 : f 0 = 0 := he .zero
    have h1 : f 1 = 1 := sub_eq_zero.mp (he .one)
    have hm (m n : ℕ) (hc : m.Coprime n) : f (m * n) = f m * f n :=
      sub_eq_zero.mp (he (.multiplicative m n hc))
    have hr (q : ℕ) (hq : q.Prime) (j : ℕ) :
        f (q ^ (j + 2)) = f q * f (q ^ (j + 1)) -
          FinitenessEulerIdentification.xi N q * f (q ^ j) :=
      sub_eq_zero.mp (he (.primePower q j hq))
    have hb : BadPrimeConditions N f := fun q hq hd => sub_eq_zero.mp (he (.bad q hq hd))
    obtain ⟨σ, hσ, hgσ⟩ := hg
    exact ⟨⟨h0, ⟨σ, hσ, hgσ⟩,
      AsymptoticClassicalEulerProduct.eulerProduct_of_arithmetic h0 h1 hgσ hm hr, hb⟩,
      sub_eq_zero.mp (he .eigenvalue)⟩
  · rintro ⟨hf, hz⟩ e
    obtain ⟨h1, hm, hr⟩ := FinitenessEulerIdentification.euler_arithmetic hf
    cases e with
    | zero => exact hf.zero
    | one => exact sub_eq_zero.mpr h1
    | eigenvalue => exact sub_eq_zero.mpr hz
    | multiplicative m n hc => exact sub_eq_zero.mpr (hm m n hc)
    | primePower q j hq => exact sub_eq_zero.mpr (hr q hq j)
    | bad q hq hd => exact sub_eq_zero.mpr (hf.bad q hq hd)

#print axioms equations_iff_eulerData

end FinitenessAllLevelEulerEquations
