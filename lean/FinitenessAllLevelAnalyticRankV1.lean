module

public import FinitenessAllLevelFunctionalChartV1
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticRank

open Complex Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem determinant_analytic {n : ℕ} {U : Set ℂ}
    (B : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, AnalyticOnNhd ℂ (fun z => B z i j) U) :
    AnalyticOnNhd ℂ (fun z => (B z).det) U := by
  intro z hz
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_prod _ (fun j _ => hB (σ j) j z hz)

/-- A finite family of analytic vector-valued functions that is independent
somewhere on a connected domain is independent in a punctured neighborhood
of every point of that domain. -/
theorem independent_punctured {n : ℕ} {U : Set ℂ} (hU : IsPreconnected U)
    {a : Fin n → ℂ → E} (ha : ∀ i, AnalyticOnNhd ℂ (a i) U)
    {z₀ w : ℂ} (hz₀ : z₀ ∈ U) (hw : w ∈ U)
    (hi : LinearIndependent ℂ (fun i => a i z₀)) :
    ∀ᶠ z in 𝓝[≠] w, LinearIndependent ℂ (fun i => a i z) := by
  classical
  obtain ⟨T, hT⟩ := (Fintype.linearCombination ℂ (fun i => a i z₀)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi.fintypeLinearCombination_injective)
  let B : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z i j => T (a j z) i
  have hB : AnalyticOnNhd ℂ (fun z => (B z).det) U := by
    apply determinant_analytic
    intro i j z hz
    exact ((ContinuousLinearMap.proj i).analyticAt _).comp
      (T.toContinuousLinearMap.analyticAt _ |>.comp (ha j z hz))
  have hB₀ : B z₀ = 1 := by
    ext i j
    have he := congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) =>
      f (Pi.single j 1) i) hT
    simpa [B, Fintype.linearCombination_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using he
  have hne : ∀ᶠ z in 𝓝[≠] w, (B z).det ≠ 0 := by
    rcases (hB w hw).eventually_eq_zero_or_eventually_ne_zero with hz | hn
    · have he := hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hw hz hz₀
      simp [hB₀] at he
    · exact hn
  filter_upwards [hne] with z hz
  have hh := Matrix.linearIndependent_cols_of_det_ne_zero hz
  exact LinearIndependent.of_comp T hh

#print axioms determinant_analytic
#print axioms independent_punctured

end FinitenessAllLevelAnalyticRank
