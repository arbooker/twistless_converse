module

public import FinitenessAllLevelFormalUniformBoundsV1
public import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelEigenvalueDegree

open Polynomial

/-- An actual polynomial representation, not only a growth assertion. -/
def DegreeBound (f : ℂ → ℂ) (j : ℕ) : Prop :=
  ∃ P : Polynomial ℂ, P.natDegree ≤ j ∧ ∀ z, P.eval z = f z

theorem constant (c : ℂ) (j : ℕ) : DegreeBound (fun _ => c) j :=
  ⟨C c, by simp, fun _ => eval_C⟩

theorem DegreeBound.const_mul {f : ℂ → ℂ} {j : ℕ} (hf : DegreeBound f j) (c : ℂ) :
    DegreeBound (fun z => c * f z) j := by
  obtain ⟨P, hP, he⟩ := hf
  exact ⟨C c * P, (natDegree_C_mul_le _ _).trans hP, fun z => by simp only [eval_mul, eval_C, he]⟩

theorem DegreeBound.sub {f g : ℂ → ℂ} {j : ℕ}
    (hf : DegreeBound f j) (hg : DegreeBound g j) : DegreeBound (fun z => f z - g z) j := by
  obtain ⟨P, hP, he⟩ := hf
  obtain ⟨Q, hQ, hf⟩ := hg
  exact ⟨P - Q, (natDegree_sub_le _ _).trans (max_le hP hQ), fun z => by simp only [eval_sub, he, hf]⟩

theorem DegreeBound.param_mul {f : ℂ → ℂ} {j : ℕ} (hf : DegreeBound f j) :
    DegreeBound (fun z => z * f z) (j + 1) := by
  obtain ⟨P, hP, he⟩ := hf
  refine ⟨X * P, ?_, fun z => by simp only [eval_mul, eval_X, he]⟩
  exact natDegree_mul_le.trans (by simpa only [natDegree_X, Nat.add_comm] using Nat.add_le_add_left hP 1)

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (j : ℕ)
    (hf : ∀ i ∈ s, DegreeBound (f i) j) : DegreeBound (fun z => ∑ i ∈ s, f i z) j := by
  classical
  have hall (i : ι) : ∃ P : Polynomial ℂ, P.natDegree ≤ j ∧ ∀ z, P.eval z = if i ∈ s then f i z else 0 := by
    by_cases hi : i ∈ s
    · simpa only [DegreeBound, ite_eq_left hi] using hf i hi
    · simpa only [DegreeBound, ite_eq_right hi] using constant 0 j
  choose P hP he using hall
  refine ⟨∑ i ∈ s, P i, natDegree_sum_le_of_forall_le _ _ (fun i _ => hP i), ?_⟩
  intro z
  simp only [eval_finsetSum]
  exact Finset.sum_congr rfl (fun i hi => by rw [he, ite_eq_left hi])

#print axioms DegreeBound.param_mul
#print axioms sum

end FinitenessAllLevelEigenvalueDegree
