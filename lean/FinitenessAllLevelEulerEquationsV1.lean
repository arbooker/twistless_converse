module

public import FinitenessAllLevelNormalizedFunctionalV1
public import FinitenessAllLevelAnalyticSubstitutionV1
public import FinitenessEulerIdentificationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelEulerEquations

open FinitenessAllLevelCoefficientFunctional FinitenessAllLevelDiskAlgebra
  FinitenessOriginalInput FinitenessAllLevelAnalyticSubstitution Set ContinuousLinearMap

/-- The individual coefficient identities used to impose the Euler data.
The index includes the actual arithmetic side conditions. -/
inductive Equation (N : ℕ) where
  | zero
  | one
  | eigenvalue
  | multiplicative (m n : ℕ) (hc : m.Coprime n)
  | primePower (q j : ℕ) (hq : q.Prime)
  | bad (q : ℕ) (hq : q.Prime) (hd : q ∣ N)

variable {R : ℝ}

def equation (N k p : ℕ) (hR : 0 < R) (e : Equation N) (zF : ℂ × space R) : ℂ :=
  let c := fun n => normalizedCLM hR k n zF.2
  match e with
  | .zero => c 0
  | .one => c 1 - 1
  | .eigenvalue => c p - zF.1
  | .multiplicative m n _ => c (m * n) - c m * c n
  | .primePower q j _ => c (q ^ (j + 2)) -
      (c q * c (q ^ (j + 1)) - (if q ∣ N then (0 : ℂ) else 1) * c (q ^ j))
  | .bad q _ _ => c q ^ 2 - (if q ^ 2 ∣ N then 0 else (q : ℂ)⁻¹)

theorem equation_analytic (N k p : ℕ) (hR : 0 < R) (e : Equation N) :
    AnalyticOnNhd ℂ (equation N k p hR e) univ := by
  intro zF _
  have hc (n : ℕ) : AnalyticAt ℂ
      (fun zF : ℂ × space R => normalizedCLM hR k n zF.2) zF :=
    ((normalizedCLM hR k n).comp (snd ℂ ℂ (space R))).analyticAt _
  have hz : AnalyticAt ℂ (fun zF : ℂ × space R => zF.1) zF :=
    (fst ℂ ℂ (space R)).analyticAt _
  cases e with
  | zero => exact hc 0
  | one => exact (hc 1).sub analyticAt_const
  | eigenvalue => exact (hc p).sub hz
  | multiplicative m n _ => exact (hc (m * n)).sub ((hc m).mul (hc n))
  | primePower q j _ =>
      exact (hc (q ^ (j + 2))).sub
        (((hc q).mul (hc (q ^ (j + 1)))).sub (analyticAt_const.mul (hc (q ^ j))))
  | bad q _ _ => exact ((hc q).pow 2).sub analyticAt_const

/-- Every original solution satisfies every equation, with its actual
prime eigenvalue and actual Banach-disk representative. -/
theorem original_equations {N k : ℕ} (p : ℕ) (hR : 0 < R) (hR1 : R < 1)
    (f : S N k) (e : Equation N) :
    equation N k p hR e (f.val p, representative N k hR hR1 f) = 0 := by
  obtain ⟨h1, hm, hr⟩ := FinitenessEulerIdentification.solution_arithmetic f.property
  cases e with
  | zero => simpa only [equation, normalized_representative] using f.property.zero
  | one => simp only [equation, normalized_representative, h1, sub_self]
  | eigenvalue => simp only [equation, normalized_representative, sub_self]
  | multiplicative m n hc =>
      simp only [equation, normalized_representative, hm m n hc, sub_self]
  | primePower q j hq =>
      simp only [equation, normalized_representative, hr q hq j, sub_self]
  | bad q hq hd =>
      simp only [equation, normalized_representative, f.property.bad q hq hd, sub_self]

/-- All Euler equations remain holomorphic on the SAME finite-dimensional
chart domain after reconstruction, even though the family is infinite. -/
theorem chart_equations {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N k p : ℕ) (hR : 0 < R) {J : ℂ → E →L[ℂ] space R} {U : Set ℂ}
    (hJ : AnalyticOnNhd ℂ J U) (e : Equation N) :
    AnalyticOnNhd ℂ (fun zv : ℂ × E => equation N k p hR e (zv.1, J zv.1 zv.2))
      (U ×ˢ univ) :=
  substitute_analytic hJ ((equation_analytic N k p hR e).mono (subset_univ _))

#print axioms equation_analytic
#print axioms original_equations
#print axioms chart_equations

end FinitenessAllLevelEulerEquations
