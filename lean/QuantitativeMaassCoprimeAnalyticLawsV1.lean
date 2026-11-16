module

public import QuantitativeMaassCoprimeTwistsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticIntegralSubgroup

namespace QuantitativeMaass

/-- The geometric primitive sum is exactly the analytic twist used by
the strict reconstruction certificate. -/
theorem analytic_twist_eq_primitive (F : ℂ → ℂ) (q : ℕ) (z : ℍ) :
    FinitenessAnalyticReconstruction.twist F q (z:ℂ)=
      primitiveTranslationSum q (fun y : ℍ => F y) z := by
  unfold FinitenessAnalyticReconstruction.twist primitiveTranslationSum FinitenessRamanujanSum.residues
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [AsymptoticCompactTranslation.label_action,AsymptoticMobiusFold.translation_action]
  simp

theorem fricke_label_coe (N : ℕ) (hN : 0<N) (z : ℍ) :
    ((frickeLabel N hN • z : ℍ):ℂ)= -1/((N:ℂ)*z) := by
  rw [frickeLabel,AsymptoticRationalBranches.ofMatrix_action,
    AsymptoticRationalBranches.realMatrix_branch]
  simpa using AsymptoticReconstructionBranch.branch_action
    (show (0:ℝ)<N by exact_mod_cast hN) 0 0 z

/-- The coprime-modulus theorem discharges the literal weight-zero
analytic law, with no prime restriction or supplied twist equation. -/
theorem coprime_analytic_law_of_modular (N q : ℕ) (hN : 0<N) (hq : 0<q)
    (hc : N.Coprime q) (F : ℂ → ℂ)
    (hmod : ∀ a : gamma N,∀ z : ℍ,F ((a.val • z : ℍ):ℂ)=F z)
    (w : ℂ) (hW : ∀ z : ℍ,w*F (-1/((N:ℂ)*z))=F z)
    (z : ℂ) (hz : 0<z.im) :
    FinitenessAnalyticReconstruction.twist F q z=
      w*FinitenessAnalyticReconstruction.twist F q (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  have hh := coprime_twist_of_modular N q hN hq hc (fun y : ℍ => F y) hmod w
    (fun y => by rw [fricke_label_coe]; exact hW y) ⟨z,hz⟩
  rw [←analytic_twist_eq_primitive,←analytic_twist_eq_primitive,fricke_label_coe] at hh
  exact hh.symm

#print axioms analytic_twist_eq_primitive
#print axioms fricke_label_coe
#print axioms coprime_analytic_law_of_modular

end QuantitativeMaass
