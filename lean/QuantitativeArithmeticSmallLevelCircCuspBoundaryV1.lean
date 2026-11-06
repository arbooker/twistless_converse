module

public import QuantitativeArithmeticSmallLevelCircCuspWeightTwoV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral

open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped InnerProduct ComplexConjugate

/-- The two half-weight normalized old embeddings have equal Petersson
norms. This is an identity of actual cusp forms, not an assumed norm bound. -/
theorem scaled_degeneracy_inner (N p m : ℕ) [NeZero N] [NeZero (p * N)]
    (hN : 0 < N) (hp : 0 < p) (f : CuspForm (level N) ((2 * m : ℕ) : ℤ)) :
    inner ℂ ((p : ℂ)^m • degeneracy N p hp ((2 * m : ℕ) : ℤ) f)
      ((p : ℂ)^m • degeneracy N p hp ((2 * m : ℕ) : ℤ) f) =
      ((level (p * N)).relIndex (level N) : ℂ) * inner ℂ f f := by
  have hinv : frickeOperator N hN ((2 * m : ℕ) : ℤ)
      (frickeOperator N hN ((2 * m : ℕ) : ℤ) f) = f :=
    frickeOperator_involutive N hN (2 * m) (even_two_mul m) f
  have he := fricke_restrict_degeneracy N p hN hp ((2 * m : ℕ) : ℤ)
    (frickeOperator N hN ((2 * m : ℕ) : ℤ) f)
  have hhalf : ((((2 * m : ℕ) : ℤ) : ℂ) / 2) = (m : ℂ) := by push_cast; ring
  rw [hinv, hhalf, Complex.cpow_natCast] at he
  have hh := inner_frickeOperator (p * N) (Nat.mul_pos hp hN) ((2 * m : ℕ) : ℤ)
    (restrict _ (level_antitone (dvd_mul_left N p)) (frickeOperator N hN _ f))
    (restrict _ (level_antitone (dvd_mul_left N p)) (frickeOperator N hN _ f))
  rw [he, restrict_inner, inner_frickeOperator] at hh
  exact hh

/-- In every even weight above two, the Eisenstein boundary eigenvalue
is excluded by positivity of the squared norm of the difference of the
two old embeddings. -/
theorem higher_boundary_eigen_zero (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 2 ≤ m)
    (f : CuspForm (level N) ((2 * m : ℕ) : ℤ))
    (hf : dilationTrace N p hp.pos ((2 * m : ℕ) : ℤ) f =
      (1 + (p : ℂ)^(2 * m - 1)) • f) : f = 0 := by
  let : NeZero (p * N) := ⟨(Nat.mul_pos hp.pos hN).ne'⟩
  have hi : (level (p * N)).relIndex (level N) = p + 1 := by
    rw [level_relIndex]
    exact AsymptoticRamifiedCosets.projective_index_coprime N p hN hp
      (hp.coprime_iff_not_dvd.mpr hpN)
  let u := restrict ((2 * m : ℕ) : ℤ) (level_antitone (dvd_mul_left N p)) f
  let w := (p : ℂ)^m • degeneracy N p hp.pos ((2 * m : ℕ) : ℤ) f
  let v := (p : ℂ)^(m - 1) • w
  have hv : v = (p : ℂ)^(2 * m - 1) • degeneracy N p hp.pos _ f := by
    dsimp [v, w]
    rw [smul_smul, ← pow_add, show m - 1 + m = 2 * m - 1 by omega]
  have huu : inner ℂ u u = (p + 1 : ℂ) * inner ℂ f f := by
    dsimp [u]
    rw [restrict_inner, hi]
    push_cast
    rfl
  have hww : inner ℂ w w = (p + 1 : ℂ) * inner ℂ f f := by
    have hh := scaled_degeneracy_inner N p m hN hp.pos f
    rw [hi] at hh
    change inner ℂ w w = ((p + 1 : ℕ) : ℂ) * inner ℂ f f at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hvv : inner ℂ v v = (p : ℂ)^(2 * m - 2) * (p + 1) * inner ℂ f f := by
    dsimp [v]
    rw [inner_smul_left, inner_smul_right, hww]
    simp only [map_pow, Complex.conj_natCast]
    rw [← mul_assoc, ← mul_assoc, ← pow_add,
      show m - 1 + (m - 1) = 2 * m - 2 by omega]
  have hvu : inner ℂ v u = (1 + (p : ℂ)^(2 * m - 1)) * inner ℂ f f := by
    have hh := dilationTrace_inner N p hp.pos ((2 * m : ℕ) : ℤ) f f
    rw [hf, inner_smul_left] at hh
    have hz : ((2 * m : ℕ) : ℤ) - 1 = ((2 * m - 1 : ℕ) : ℤ) := by omega
    rw [hz, zpow_natCast] at hh
    simpa [hv, u, inner_smul_left] using hh.symm
  have huv : inner ℂ u v = inner ℂ v u := by
    rw [← inner_conj_symm, hvu]
    simp
  have he : inner ℂ (v - u) (v - u) =
      ((p : ℂ) - 1) * (1 - (p : ℂ)^(2 * m - 2)) * inner ℂ f f := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, huv, hvu, hvv, huu]
    rw [show 2 * m - 1 = (2 * m - 2) + 1 by omega, pow_succ]
    ring
  have heR := congrArg Complex.re he
  have hs : ((p : ℂ) - 1) * (1 - (p : ℂ)^(2 * m - 2)) =
      (((p : ℝ) - 1) * (1 - (p : ℝ)^(2 * m - 2)) : ℝ) := by push_cast; rfl
  rw [hs, Complex.mul_re] at heR
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at heR
  have hpos : 1 < (p : ℝ)^(2 * m - 2) := one_lt_pow₀ (by exact_mod_cast hp.one_lt)
    (by omega)
  have hn : 0 ≤ (inner ℂ (v - u) (v - u)).re := inner_self_nonneg (𝕜 := ℂ)
  have hff : 0 ≤ (inner ℂ f f).re := inner_self_nonneg (𝕜 := ℂ)
  have hpr : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hneg : ((p : ℝ) - 1) * (1 - (p : ℝ)^(2 * m - 2)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hz : (inner ℂ f f).re = 0 := by nlinarith
  have him : (inner ℂ f f).im = 0 := inner_self_im (𝕜 := ℂ) f
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (Complex.ext hz him)

#print axioms scaled_degeneracy_inner
#print axioms higher_boundary_eigen_zero

end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
