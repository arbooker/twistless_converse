module

public import AsymptoticClassicalEigenPrimeV1
public import AsymptoticClassicalEigenCountV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEigenbasis

open Module

section Algebra

variable {E ι : Type*} [AddCommGroup E] [Module ℂ E]

/-- A vanishing-first-coefficient theorem on joint eigenvectors suffices
for multiplicity one; extraction by operators of every index is unnecessary. -/
theorem joint_vectors_proportional_of_kernel (T : ι → E →ₗ[ℂ] E)
    (first : E →ₗ[ℂ] ℂ)
    (hkernel : ∀ (v : E) (χ : ι → ℂ), (∀ i, T i v = χ i • v) → first v = 0 → v = 0)
    {v w : E} {χ : ι → ℂ}
    (hv : ∀ i, T i v = χ i • v) (hw : ∀ i, T i w = χ i • w) :
    first w • v = first v • w := by
  apply sub_eq_zero.mp
  apply hkernel _ χ
  · intro i
    rw [map_sub, map_smul, map_smul, hv i, hw i]
    module
  · simp only [map_sub, map_smul, smul_eq_mul]
    ring

/-- Multiplicity one makes a commuting involution diagonal with sign
eigenvalues, using only the joint first-coefficient kernel theorem. -/
theorem commuting_involution_sign_of_kernel (T : ι → E →ₗ[ℂ] E)
    (first : E →ₗ[ℂ] ℂ)
    (hkernel : ∀ (v : E) (χ : ι → ℂ), (∀ i, T i v = χ i • v) → first v = 0 → v = 0)
    (Q : E →ₗ[ℂ] E) (hcomm : ∀ i, Commute (T i) Q) (hinv : Function.Involutive Q)
    {v : E} (hone : first v = 1) {χ : ι → ℂ} (heigen : ∀ i, T i v = χ i • v) :
    ∃ e : ℂ, (e = 1 ∨ e = -1) ∧ Q v = e • v := by
  have hQ (i : ι) : T i (Q v) = χ i • Q v := by
    have h := congrArg (fun A : E →ₗ[ℂ] E => A v) (hcomm i).eq
    change T i (Q v) = Q (T i v) at h
    rw [h, heigen i, map_smul]
  have h := joint_vectors_proportional_of_kernel T first hkernel heigen hQ
  rw [hone, one_smul] at h
  have he : Q v = first (Q v) • v := h.symm
  refine ⟨first (Q v), ?_, he⟩
  apply sq_eq_one_iff.mp
  have hh := congrArg (fun w => first (Q w)) he
  rw [hinv v, map_smul, map_smul, hone] at hh
  simpa only [smul_eq_mul, pow_two] using hh.symm

end Algebra

section Spectrum

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Spectral normalization needs only injectivity of the first
coefficient on each joint eigenspace. -/
theorem exists_normalized_joint_family_of_kernel (T : ι → E →ₗ[ℂ] E)
    (hT : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise fun i j => Commute (T i) (T j))
    (first : E →ₗ[ℂ] ℂ)
    (hkernel : ∀ (v : E) (χ : ι → ℂ), (∀ i, T i v = χ i • v) → first v = 0 → v = 0) :
    ∃ b : Fin (finrank ℂ E) → E, Function.Injective b ∧
      (∀ j, first (b j) = 1) ∧
      ∀ j, ∃ χ : ι → ℂ, ∀ i, T i (b j) = χ i • b j := by
  obtain ⟨b, hb, he⟩ := exists_joint_family T hT hcomm
  have hfirst : ∀ j, first (b j) ≠ 0 := by
    intro j hj
    obtain ⟨χ, hχ⟩ := he j
    exact hb.ne_zero j (hkernel (b j) χ hχ hj)
  refine ⟨fun j => normalizedVector first (b j),
    normalizedVector_injective hb first hfirst,
    fun j => first_normalizedVector first (hfirst j), ?_⟩
  intro j
  obtain ⟨χ, hχ⟩ := he j
  exact ⟨χ, normalizedVector_eigen T first hχ⟩

/-- The prime coefficient laws suffice for a full normalized eigenfamily.
No T_n for composite indices and no all-index extraction hypothesis occur. -/
theorem exists_normalized_prime_family (T : Nat.Primes → E →ₗ[ℂ] E)
    (hT : ∀ p, (T p).IsSymmetric) (hcomm : Pairwise fun p q => Commute (T p) (T q))
    (coeff : ℕ → E →ₗ[ℂ] ℂ) (b : Nat.Primes → ℂ)
    (hzero : ∀ v, coeff 0 v = 0)
    (hsep : ∀ v, (∀ n, coeff n v = 0) → v = 0)
    (hcoeff : ∀ (p : Nat.Primes) (n : ℕ) (v : E),
      coeff n (T p v) = coeff (p.val*n) v +
        b p * (if p.val ∣ n then coeff (n/p.val) v else 0)) :
    ∃ v : Fin (finrank ℂ E) → E, Function.Injective v ∧
      (∀ j, coeff 1 (v j) = 1) ∧
      ∀ j, ∃ χ : Nat.Primes → ℂ, ∀ p, T p (v j) = χ p • v j := by
  apply exists_normalized_joint_family_of_kernel T hT hcomm (coeff 1)
  intro v χ hχ h1
  exact prime_joint_first_kernel T coeff b hzero hsep hcoeff hχ h1

end Spectrum

#print axioms joint_vectors_proportional_of_kernel
#print axioms commuting_involution_sign_of_kernel
#print axioms exists_normalized_joint_family_of_kernel
#print axioms exists_normalized_prime_family

end AsymptoticClassicalEigenbasis
