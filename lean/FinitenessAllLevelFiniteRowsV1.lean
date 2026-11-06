module

public import FinitenessAllLevelAnalyticRankV1
public import Mathlib.Order.SuccPred.Archimedean

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticRank

open Complex Set Filter
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem select_basis (v : ι → E) :
    ∃ b : Fin (Module.finrank ℂ (Submodule.span ℂ (range v))) → ι,
      Submodule.span ℂ (range (fun j => v (b j))) = Submodule.span ℂ (range v) ∧
      LinearIndependent ℂ (fun j => v (b j)) := by
  obtain ⟨u, hu, hs, hi⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (range v)
  choose b hb using hu
  have he : (fun j => v (b j)) = u := funext hb
  exact ⟨b, he ▸ hs, he ▸ hi⟩

/-- An arbitrary family of analytic vectors in a fixed finite-dimensional
space has its pointwise spans generated locally by one finite subfamily.
The parameter is one complex variable and the analytic domain is common. -/
theorem finite_rows_local {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (a : ι → ℂ → E) (ha : ∀ i, AnalyticOnNhd ℂ (a i) U) {w : ℂ} (hw : w ∈ U) :
    ∃ s : Finset ι, ∀ᶠ z in 𝓝 w,
      Submodule.span ℂ ((fun i => a i z) '' (s : Set ι)) =
        Submodule.span ℂ (range (fun i => a i z)) := by
  classical
  let S : ℂ → Submodule ℂ E := fun z => Submodule.span ℂ (range (fun i => a i z))
  have hbdd : BddAbove ((fun z => Module.finrank ℂ (S z)) '' U) :=
    ⟨Module.finrank ℂ E, by rintro r ⟨z, _, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨r, ⟨z₀, hz₀, hr⟩, hmax⟩ := hbdd.exists_isGreatest_of_nonempty
    ⟨Module.finrank ℂ (S w), w, hw, rfl⟩
  obtain ⟨b, _, hi⟩ := select_basis (fun i => a i z₀)
  obtain ⟨c, hc, _⟩ := select_basis (fun i => a i w)
  let s : Finset ι := Finset.univ.image b ∪ Finset.univ.image c
  have hsub (z : ℂ) :
      Submodule.span ℂ ((fun i => a i z) '' (s : Set ι)) ≤ S z := by
    apply Submodule.span_mono
    rintro v ⟨i, _, rfl⟩
    exact mem_range_self i
  have hbsub (z : ℂ) : Submodule.span ℂ (range (fun j => a (b j) z)) ≤
      Submodule.span ℂ ((fun i => a i z) '' (s : Set ι)) := by
    apply Submodule.span_mono
    rintro v ⟨j, rfl⟩
    exact ⟨b j, by simp [s], rfl⟩
  have hcsub : S w ≤ Submodule.span ℂ ((fun i => a i w) '' (s : Set ι)) := by
    change Submodule.span ℂ (range (fun i => a i w)) ≤ _
    rw [← hc]
    apply Submodule.span_mono
    rintro v ⟨j, rfl⟩
    exact ⟨c j, by simp [s], rfl⟩
  have hind := independent_punctured hconn (fun j => ha (b j)) hz₀ hw hi
  rw [eventually_nhdsWithin_iff] at hind
  refine ⟨s, ?_⟩
  filter_upwards [hind, hU.mem_nhds hw] with z hz hzU
  apply le_antisymm (hsub z)
  by_cases he : z = w
  · subst z
    exact hcsub
  · have hindz := hz he
    have heq : Submodule.span ℂ (range (fun j => a (b j) z)) = S z := by
      apply Submodule.eq_of_le_of_finrank_le ((hbsub z).trans (hsub z))
      have hdim := finrank_span_eq_card hindz
      simp only [Fintype.card_fin] at hdim
      rw [hdim]
      exact (hmax ⟨z, hzU, rfl⟩).trans_eq hr.symm
    rw [← heq]
    exact hbsub z

#print axioms select_basis
#print axioms finite_rows_local

end FinitenessAllLevelAnalyticRank
