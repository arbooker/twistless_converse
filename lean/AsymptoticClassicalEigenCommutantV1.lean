module

public import AsymptoticClassicalEigenNormalizationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

variable {E ι : Type*} [AddCommGroup E] [Module ℂ E]

/-- First-coefficient multiplicity one forces every commuting operator
to act scalarly on a normalized joint eigenvector. -/
theorem commuting_operator_eigen (T : ι → E →ₗ[ℂ] E)
    (first : E →ₗ[ℂ] ℂ) (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0)
    (Q : E →ₗ[ℂ] E) (hcomm : ∀ i, Commute (T i) Q)
    {v : E} (hone : first v = 1) {χ : ι → ℂ}
    (heigen : ∀ i, T i v = χ i • v) : Q v = first (Q v) • v := by
  have hQ (i : ι) : T i (Q v) = χ i • Q v := by
    have h := congrArg (fun A : E →ₗ[ℂ] E => A v) (hcomm i).eq
    change T i (Q v) = Q (T i v) at h
    rw [h, heigen i, map_smul]
  have h := joint_vectors_proportional T first coeff hcoeff hsep heigen hQ
  rw [hone, one_smul] at h
  exact h.symm

/-- An involution commuting with the coefficient-extracting operators
has sign eigenvalues on their normalized joint eigenvectors. -/
theorem commuting_involution_sign (T : ι → E →ₗ[ℂ] E)
    (first : E →ₗ[ℂ] ℂ) (coeff : ι → E →ₗ[ℂ] ℂ)
    (hcoeff : ∀ i v, first (T i v) = coeff i v)
    (hsep : ∀ v, (∀ i, coeff i v = 0) → v = 0)
    (Q : E →ₗ[ℂ] E) (hcomm : ∀ i, Commute (T i) Q)
    (hinv : Function.Involutive Q)
    {v : E} (hone : first v = 1) {χ : ι → ℂ}
    (heigen : ∀ i, T i v = χ i • v) :
    ∃ e : ℂ, (e = 1 ∨ e = -1) ∧ Q v = e • v := by
  have hQ := commuting_operator_eigen T first coeff hcoeff hsep Q hcomm hone heigen
  refine ⟨first (Q v), ?_, hQ⟩
  apply sq_eq_one_iff.mp
  have h := congrArg (fun w => first (Q w)) hQ
  rw [hinv v, map_smul, map_smul, hone] at h
  simpa only [smul_eq_mul, pow_two] using h.symm

#print axioms commuting_operator_eigen
#print axioms commuting_involution_sign

end AsymptoticClassicalEigenbasis
