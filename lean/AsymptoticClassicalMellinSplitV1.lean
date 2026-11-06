module

public import AsymptoticClassicalMellinBoundV1
public import FinitenessFiniteOrderClosureV1
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open Complex MeasureTheory Set

theorem upperMellin_eq_indicator (f : ℝ → ℂ) (s : ℂ) :
    upperMellin f s = mellin ((Ioi 1).indicator f) s := by
  have he : (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Ioi 1).indicator f t) =
      (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) := by
    funext t
    exact (indicator_mul_right (Ioi 1) (fun t : ℝ => (t : ℂ) ^ (s - 1)) f).symm
  rw [mellin, he, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))]
  rfl

/-- The lower half of a strong functional-equation pair is the reflected
 upper Mellin transform of its partner. -/
theorem lowerMellin_eq (P : WeakFEPair ℂ) (s : ℂ) :
    mellin ((Ioo 0 1).indicator P.f) s = P.ε * upperMellin P.g ((P.k : ℂ) - s) := by
  have he : mellin ((Ioo 0 1).indicator P.f) s =
      mellin (fun t : ℝ => (t : ℂ) ^ (-(P.k : ℂ)) •
        (P.ε • (Ioi 1).indicator P.g t⁻¹)) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (t : ℂ) ^ (s - 1) • (Ioo 0 1).indicator P.f t =
      (t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (-(P.k : ℂ)) • (P.ε • (Ioi 1).indicator P.g t⁻¹))
    apply congrArg (fun w : ℂ => (t : ℂ) ^ (s - 1) • w)
    by_cases h1 : t < 1
    · have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h1
      rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, h1⟩),
        indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hi)]
      have hh := P.h_feq t⁻¹ (inv_pos.mpr ht)
      rw [one_div, inv_inv] at hh
      rw [hh, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
        Complex.ofReal_cpow ht.le, Complex.ofReal_neg]
      simp only [smul_eq_mul]
      ring
    · have hi : t⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr (le_of_not_gt h1)
      rw [indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun h => h1 h.2),
        indicator_of_notMem (show t⁻¹ ∉ Ioi (1 : ℝ) from not_lt.mpr hi), smul_zero, smul_zero]
  rw [he, mellin_cpow_smul, mellin_const_smul, mellin_comp_inv]
  rw [show -(s + -(P.k : ℂ)) = (P.k : ℂ) - s by ring, ← upperMellin_eq_indicator]
  rfl

/-- Splitting at height one isolates two exponentially decaying tails. -/
theorem strongPair_mellin_split (P : WeakFEPair ℂ) (hP : IsStrongFEPair P) (s : ℂ) :
    P.Λ s = upperMellin P.f s + P.ε * upperMellin P.g ((P.k : ℂ) - s) := by
  have hu : MellinConvergent ((Ioi 1).indicator P.f) s := by
    simpa only [MellinConvergent, ← indicator_smul] using
      ((hP.hasMellin s).1).indicator measurableSet_Ioi
  have hl : MellinConvergent ((Ioo 0 1).indicator P.f) s := by
    simpa only [MellinConvergent, ← indicator_smul] using
      ((hP.hasMellin s).1).indicator measurableSet_Ioo
  have hf : P.f_modif = fun t => (Ioi 1).indicator P.f t + (Ioo 0 1).indicator P.f t := by
    simp only [WeakFEPair.f_modif, hP.hf₀, hP.hg₀, sub_zero, smul_zero]
    rfl
  simp only [WeakFEPair.Λ, WeakFEPair.Λ₀, hP.hf₀, hP.hg₀, smul_zero, sub_zero]
  rw [hf, (hasMellin_add hu hl).2, ← upperMellin_eq_indicator, lowerMellin_eq]

theorem finiteOrder_reflect {F : ℂ → ℂ} (hF : FinitenessFiniteOrder.Bound F) (a : ℂ) :
    FinitenessFiniteOrder.Bound (fun s => F (a - s)) := by
  obtain ⟨A, hA, d, hb⟩ := FinitenessInputBounds.bound_shift hF a
  refine ⟨A, hA, d, fun s => ?_⟩
  simpa only [norm_neg, sub_eq_add_neg, add_comm] using hb (-s)

theorem strongPair_finiteOrder (P : WeakFEPair ℂ) (hP : IsStrongFEPair P)
    {Cf Cg cf cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hcf : 0 < cf) (hcg : 0 < cg)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖P.f t‖ ≤ Cf * Real.exp (-cf * t))
    (hg : ∀ t : ℝ, 1 ≤ t → ‖P.g t‖ ≤ Cg * Real.exp (-cg * t)) :
    FinitenessFiniteOrder.Bound P.Λ := by
  have h1 := upperMellin_finiteOrder P.f hCf hcf hf
  have h2 := finiteOrder_reflect (upperMellin_finiteOrder P.g hCg hcg hg) (P.k : ℂ)
  have hh := FinitenessFiniteOrderClosure.add h1
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const P.ε) h2)
  have he : P.Λ = fun s => upperMellin P.f s + P.ε * upperMellin P.g ((P.k : ℂ) - s) :=
    funext (strongPair_mellin_split P hP)
  rw [he]
  exact hh

#print axioms upperMellin_eq_indicator
#print axioms lowerMellin_eq
#print axioms strongPair_mellin_split
#print axioms finiteOrder_reflect
#print axioms strongPair_finiteOrder

end AsymptoticClassicalLSeries
