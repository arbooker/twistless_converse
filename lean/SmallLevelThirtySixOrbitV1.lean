module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup
open scoped ModularForm MatrixGroups

theorem sub_slash (f g : ℍ → ℂ) (k : ℤ) (A : SL(2,ℤ)) :
    (f-g) ∣[k] A=(f ∣[k] A)-(g ∣[k] A) := by
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash]

theorem slash_neg_one_even (f : ℍ → ℂ) (m : ℕ) :
    f ∣[((2*m : ℕ) : ℤ)] (-1 : SL(2,ℤ))=f := by
  funext z
  rw [ModularForm.SL_slash_apply]
  simp only [ModularGroup.SL_neg_smul, one_smul]
  rw [show denom (-1 : SL(2,ℤ)) z=(-1 : ℂ) by
    norm_num [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL]]
  rw [zpow_neg, zpow_natCast, pow_mul]
  norm_num

theorem slash_S_twice_even (f : ℍ → ℂ) (m : ℕ) :
    (f ∣[((2*m : ℕ) : ℤ)] S) ∣[((2*m : ℕ) : ℤ)] S=f := by
  rw [← SlashAction.slash_mul, show S*S=(-1 : SL(2,ℤ)) by decide]
  exact slash_neg_one_even f m

theorem slash_TST_even (f : ℍ → ℂ) (m : ℕ) :
    ((f ∣[((2*m : ℕ) : ℤ)] T) ∣[((2*m : ℕ) : ℤ)] S) ∣[((2*m : ℕ) : ℤ)] T =
      ((f ∣[((2*m : ℕ) : ℤ)] S) ∣[((2*m : ℕ) : ℤ)] T⁻¹) ∣[((2*m : ℕ) : ℤ)] S := by
  have hm : T*S*T=(-1 : SL(2,ℤ))*(S*T⁻¹*S) := by decide
  have hh := congrArg (fun A : SL(2,ℤ) => f ∣[((2*m : ℕ) : ℤ)] A) hm
  simpa only [SlashAction.slash_mul, slash_neg_one_even] using hh

/-- The remaining extension in the negative Fricke-sign sector. -/
def obstruction (m : ℕ) (g : ℍ → ℂ) : ℍ → ℂ :=
  (g ∣[((2*m : ℕ) : ℤ)] T) + ((g ∣[((2*m : ℕ) : ℤ)] T) ∣[((2*m : ℕ) : ℤ)] S)

/-- Fourier support at level 36 and the negative Fricke sign force the
extension H to be invariant under S and T. No independence of the three
orbit functions or modularity of g is assumed. -/
theorem obstruction_invariant (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m : ℕ) : ℤ)] T) ∣[((2*m : ℕ) : ℤ)] T =
      (g ∣[((2*m : ℕ) : ℤ)] T)-g)
    (hS : g ∣[((2*m : ℕ) : ℤ)] S = -g) :
    (obstruction m g ∣[((2*m : ℕ) : ℤ)] S=obstruction m g) ∧
      (obstruction m g ∣[((2*m : ℕ) : ℤ)] T=obstruction m g) := by
  have hi : g ∣[((2*m : ℕ) : ℤ)] T⁻¹=g-(g ∣[((2*m : ℕ) : ℤ)] T) := by
    have hh := congrArg (fun f : ℍ → ℂ => f ∣[((2*m : ℕ) : ℤ)] T⁻¹) hT
    simp only [sub_slash, ← SlashAction.slash_mul,
      mul_assoc, mul_inv_cancel, mul_one, SlashAction.slash_one] at hh
    linear_combination hh
  have hhT : ((g ∣[((2*m : ℕ) : ℤ)] T) ∣[((2*m : ℕ) : ℤ)] S)
      ∣[((2*m : ℕ) : ℤ)] T = g + ((g ∣[((2*m : ℕ) : ℤ)] T) ∣[((2*m : ℕ) : ℤ)] S) := by
    rw [slash_TST_even, hS, SlashAction.neg_slash, hi,
      SlashAction.neg_slash, sub_slash, hS]
    abel
  constructor
  · rw [obstruction, SlashAction.add_slash, slash_S_twice_even]
    exact add_comm _ _
  · rw [obstruction, SlashAction.add_slash, hT, hhT]
    abel

theorem obstruction_modular (m : ℕ) (g : ℍ → ℂ)
    (hT : (g ∣[((2*m : ℕ) : ℤ)] T) ∣[((2*m : ℕ) : ℤ)] T =
      (g ∣[((2*m : ℕ) : ℤ)] T)-g)
    (hS : g ∣[((2*m : ℕ) : ℤ)] S = -g) :
    ∀ γ : SL(2,ℤ), obstruction m g ∣[((2*m : ℕ) : ℤ)] γ=obstruction m g :=
  SlashInvariantForm.slash_action_generators_SL2Z
    (obstruction_invariant m g hT hS).1 (obstruction_invariant m g hT hS).2

#print axioms slash_neg_one_even
#print axioms slash_TST_even
#print axioms obstruction_invariant
#print axioms obstruction_modular

end SmallLevelThirtySix
