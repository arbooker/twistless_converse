module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLevelOne
open UpperHalfPlane ModularGroup
open scoped ModularForm MatrixGroups

theorem slash_power_eigen (f : ℍ → ℂ) (k : ℤ) (g : SL(2,ℤ)) (w : ℂ)
    (hg : f ∣[k] g=w • f) (n : ℕ) : f ∣[k] (g^n)=w^n • f := by
  induction n with
  | zero => simp only [pow_zero,SlashAction.slash_one,one_smul]
  | succ n ih =>
    rw [pow_succ,SlashAction.slash_mul,ih,ModularForm.SL_smul_slash,hg,smul_smul,pow_succ]

/-- The exact modular-group relation rules out a nontrivial sign on S
for a period-one function. No nonzero-function hypothesis is needed. -/
theorem signed_S_is_fixed (f : ℍ → ℂ) (k : ℤ) (w : ℂ) (hw : w^2=1)
    (hS : f ∣[k] S=w • f) (hT : f ∣[k] T=f) : f ∣[k] S=f := by
  have hST : f ∣[k] (S*T)=w • f := by
    rw [SlashAction.slash_mul,hS,ModularForm.SL_smul_slash,hT]
  have hrel : (S*T)^3=S^2 := by decide
  have hh := congrArg (fun g : SL(2,ℤ) => f ∣[k] g) hrel
  rw [slash_power_eigen f k (S*T) w hST 3,slash_power_eigen f k S w hS 2,
    show w^3=w by rw [pow_succ,hw,one_mul],hw,one_smul] at hh
  exact hS.trans hh

theorem signed_S_periodic_modular (f : ℍ → ℂ) (k : ℤ) (w : ℂ) (hw : w^2=1)
    (hS : f ∣[k] S=w • f) (hT : f ∣[k] T=f) :
    ∀ g : SL(2,ℤ), f ∣[k] g=f :=
  SlashInvariantForm.slash_action_generators_SL2Z (signed_S_is_fixed f k w hw hS hT) hT

#print axioms signed_S_is_fixed
#print axioms signed_S_periodic_modular
end QuantitativeEulerEndpointLevelOne
