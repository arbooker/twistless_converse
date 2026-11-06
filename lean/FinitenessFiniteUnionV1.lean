module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Set.Card

set_option autoImplicit false

public section

namespace FinitenessFiniteUnion

variable {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_sup_le (s : Finset J) (W : J → Submodule K V)
    [∀ j, FiniteDimensional K (W j)] :
    Module.finrank K ↥(s.sup W) ≤ ∑ j ∈ s, Module.finrank K (W j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [Finset.sup_insert, Finset.sum_insert hj]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
        (Nat.add_le_add_left ih _)

/-- An independent family covered by finitely many finite-dimensional
subspaces is bounded by the SUM of their dimensions. This retains the
different leading constants needed for the asymptotic sector argument. -/
theorem bound_sum [Fintype J] (W : J → Submodule K V)
    [∀ j, FiniteDimensional K (W j)] (f : I → V)
    (hf : LinearIndependent K f) (hmem : ∀ i, ∃ j, f i ∈ W j) :
    Finite I ∧ Nat.card I ≤ ∑ j : J, Module.finrank K (W j) := by
  classical
  let U := Finset.univ.sup W
  have hm : ∀ i, f i ∈ U := by
    intro i
    obtain ⟨j,hj⟩ := hmem i
    exact (Finset.le_sup (f := W) (Finset.mem_univ j)) hj
  let g : I → U := fun i => ⟨f i,hm i⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp U.subtype
    exact hf
  have hfinite : Finite I := hg.finite
  let := hfinite
  let := Fintype.ofFinite I
  refine ⟨hfinite, ?_⟩
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card I ≤ Module.finrank K U := hg.fintype_card_le_finrank
    _ ≤ ∑ j : J, Module.finrank K (W j) := finrank_sup_le Finset.univ W

/-- Uniform-dimension specialization of `bound_sum`. -/
theorem bound [Fintype J] (W : J → Submodule K V)
    [∀ j, FiniteDimensional K (W j)] (f : I → V)
    (hf : LinearIndependent K f) (hmem : ∀ i, ∃ j, f i ∈ W j)
    (d : ℕ) (hd : ∀ j, Module.finrank K (W j) ≤ d) :
    Finite I ∧ Nat.card I ≤ Fintype.card J*d := by
  obtain ⟨hfinite,hcard⟩ := bound_sum W f hf hmem
  refine ⟨hfinite,hcard.trans ?_⟩
  calc
    (∑ j : J, Module.finrank K (W j)) ≤ ∑ _j : J, d := Finset.sum_le_sum fun j _ => hd j
    _ = Fintype.card J*d := by simp

#print axioms bound_sum
#print axioms bound

end FinitenessFiniteUnion
