module

public import QuantitativeArithmeticSmallLevelCircCuspDegeneracyV1
public import AsymptoticClassicalHeckeFrickeV1
public import AsymptoticClassicalMultiplicityOrdinaryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral

open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped InnerProduct ComplexConjugate

theorem restrict_inner (N p : ℕ) [NeZero N] [NeZero (p * N)]
    (k : ℤ) (f g : CuspForm (level N) k) :
    inner ℂ (restrict k (level_antitone (dvd_mul_left N p)) f)
      (restrict k (level_antitone (dvd_mul_left N p)) g) =
      ((level (p * N)).relIndex (level N) : ℂ) * inner ℂ f g := by
  rw [← trace_adjoint (p * N) N k (dvd_mul_left N p)]
  let : (level (p * N)).IsFiniteRelIndex (level N) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * N))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).symm).1
  have ht : arithmeticTrace (level (p * N)) (level N) k
      (restrict k (level_antitone (dvd_mul_left N p)) f) =
      ((level (p * N)).relIndex (level N) : ℂ) • f :=
    trace_restrict k (level_antitone (dvd_mul_left N p)) f
  rw [ht, inner_smul_left]
  simp

/-- At weight two the Eisenstein eigenvalue p+1 is absent from the cusp
space. Equality in the trace/degeneracy bound would identify the two old
embeddings, contradicted by their actual Fourier coefficients. -/
theorem weight_two_boundary_eigen_zero (N p : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (level N) 2)
    (hf : dilationTrace N p hp.pos 2 f = (p + 1 : ℂ) • f) : f = 0 := by
  let : NeZero (p * N) := ⟨(Nat.mul_pos hp.pos hN).ne'⟩
  have hi : (level (p * N)).relIndex (level N) = p + 1 := by
    rw [level_relIndex]
    exact AsymptoticRamifiedCosets.projective_index_coprime N p hN hp
      (hp.coprime_iff_not_dvd.mpr hpN)
  let u := restrict (2 : ℤ) (level_antitone (dvd_mul_left N p)) f
  let v := (p : ℂ) • degeneracy N p hp.pos 2 f
  have huu : inner ℂ u u = (p + 1 : ℂ) * inner ℂ f f := by
    dsimp [u]
    rw [restrict_inner, hi]
    push_cast
    rfl
  have hvu : inner ℂ v u = (p + 1 : ℂ) * inner ℂ f f := by
    have hh := dilationTrace_inner N p hp.pos 2 f f
    rw [hf, inner_smul_left] at hh
    simpa [v, u, inner_smul_left] using hh.symm
  have hvv : inner ℂ v v = (p + 1 : ℂ) * inner ℂ f f := by
    have he := fricke_restrict_degeneracy N p hN hp.pos 2
      (frickeOperator N hN 2 f)
    have hinv : frickeOperator N hN (2 : ℤ) (frickeOperator N hN (2 : ℤ) f) = f :=
      frickeOperator_involutive N hN 2 (by decide) f
    rw [hinv] at he
    norm_num at he
    have hh := inner_frickeOperator (p * N) (Nat.mul_pos hp.pos hN) 2
      (restrict 2 (level_antitone (dvd_mul_left N p)) (frickeOperator N hN 2 f))
      (restrict 2 (level_antitone (dvd_mul_left N p)) (frickeOperator N hN 2 f))
    rw [he, restrict_inner, hi, inner_frickeOperator] at hh
    simpa [v] using hh
  have huv : inner ℂ u v = inner ℂ v u := by
    rw [← inner_conj_symm, hvu]
    simp
  have he : v = u := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_left, inner_sub_right, inner_sub_right, huv, hvu, hvv, huu]
    ring
  exact degeneracy_proportional_zero N p hp.one_lt 2 (p : ℂ) f he

#print axioms restrict_inner
#print axioms weight_two_boundary_eigen_zero

end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
