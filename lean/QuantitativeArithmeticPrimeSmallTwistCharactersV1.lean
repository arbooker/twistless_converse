module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

/-- Exact reconstruction on the unit residue classes from all characters,
including imprimitive characters. No primitive-character restriction is used. -/
theorem character_reconstruction (q : ℕ) [NeZero q]
    (F : (ZMod q)ˣ → ℂ) (a : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q,
      χ ((a : ZMod q)⁻¹) * ∑ b : (ZMod q)ˣ, χ (b : ZMod q) * F b) =
      (q.totient : ℂ) * F a := by
  classical
  calc
    _ = ∑ b : (ZMod q)ˣ,
        (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ (b : ZMod q)) * F b := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = ∑ b : (ZMod q)ˣ, (if a = b then (q.totient : ℂ) else 0) * F b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
      simp only [Units.val_inj]
    _ = _ := by simp

/-- Equality of all character-weighted sums forces equality of every
individual additive branch. -/
theorem individual_eq_of_all_character_sums (q : ℕ) [NeZero q]
    (F G : (ZMod q)ˣ → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ q,
      (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * F a) =
      ∑ a : (ZMod q)ˣ, χ (a : ZMod q) * G a) : F = G := by
  funext a
  have heq : (q.totient : ℂ) * F a = (q.totient : ℂ) * G a := by
    rw [← character_reconstruction q F a, ← character_reconstruction q G a]
    simp_rw [h]
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  exact mul_left_cancel₀ htot heq

theorem individual_function_eq_of_all_character_sums {X : Type*}
    (q : ℕ) [NeZero q] (F G : (ZMod q)ˣ → X → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ q, ∀ z : X,
      (∑ a : (ZMod q)ˣ, χ (a : ZMod q) * F a z) =
      ∑ a : (ZMod q)ˣ, χ (a : ZMod q) * G a z) : F = G := by
  funext a z
  exact congrFun (individual_eq_of_all_character_sums q
    (fun b => F b z) (fun b => G b z) (fun χ => h χ z)) a

#print axioms character_reconstruction
#print axioms individual_function_eq_of_all_character_sums

end QuantitativeArithmeticPrimeSmallTwist
