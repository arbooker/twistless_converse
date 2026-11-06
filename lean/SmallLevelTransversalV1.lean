module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public section

namespace SmallLevelGenerators

open Matrix ModularGroup
open scoped MatrixGroups

def lower (N : ℕ) : SL(2,ℤ) :=
  ⟨!![1,0; (N:ℤ),1], by simp [Matrix.det_fin_two]⟩

def reduction (N : ℕ) : SL(2,ℤ) →* SL(2,ZMod N) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod N))

/-- A Schreier transversal with checked S- and T-edges controls every word
in the modular group, including inverse letters. -/
theorem transversal_lift {G : Type*} [Group G] (r : SL(2,ℤ) →* G)
    (rep : G → SL(2,ℤ)) (K : Subgroup SL(2,ℤ))
    (hS : ∀ A, rep A*S*(rep (A*r S))⁻¹ ∈ K)
    (hT : ∀ A, rep A*T*(rep (A*r T))⁻¹ ∈ K)
    (γ : SL(2,ℤ)) : ∀ A, rep A*γ*(rep (A*r γ))⁻¹ ∈ K := by
  have hmem : γ ∈ Subgroup.closure {S,T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | mem γ hγ =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl
    · exact hS
    · exact hT
  | one => intro A; simp
  | mul γ δ _ _ ihγ ihδ =>
    intro A
    have h := K.mul_mem (ihγ A) (ihδ (A*r γ))
    simpa only [map_mul, mul_assoc, inv_mul_cancel_left] using h
  | inv γ _ ih =>
    intro A
    have h := K.inv_mem (ih (A*(r γ)⁻¹))
    simpa only [map_inv, mul_assoc, inv_mul_cancel, mul_one,
      _root_.mul_inv_rev, inv_inv] using h

theorem transversal_mem {G : Type*} [Group G] (r : SL(2,ℤ) →* G)
    (rep : G → SL(2,ℤ)) (K : Subgroup SL(2,ℤ))
    (hS : ∀ A, rep A*S*(rep (A*r S))⁻¹ ∈ K)
    (hT : ∀ A, rep A*T*(rep (A*r T))⁻¹ ∈ K)
    (h1 : rep 1=1) (γ : SL(2,ℤ)) (hγ : rep (r γ)=1) : γ ∈ K := by
  simpa only [one_mul, h1, hγ, inv_one, mul_one] using
    transversal_lift r rep K hS hT γ 1

def letter (N : ℕ) : Fin 5 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower N
  | 3 => (lower N)⁻¹
  | 4 => -1

def word (N : ℕ) (w : List (Fin 5)) : SL(2,ℤ) := (w.map (letter N)).prod

theorem word_mem (N : ℕ) (K : Subgroup SL(2,ℤ))
    (hT : T ∈ K) (hU : lower N ∈ K) (hZ : -1 ∈ K) (w : List (Fin 5)) :
    word N w ∈ K := by
  have hl (i : Fin 5) : letter N i ∈ K := by
    fin_cases i
    · exact hT
    · exact K.inv_mem hT
    · exact hU
    · exact K.inv_mem hU
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

#print axioms transversal_lift
#print axioms transversal_mem
#print axioms word_mem

end SmallLevelGenerators
