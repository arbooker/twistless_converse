module

public import AsymptoticClassicalHeckeSwapV1
public import AsymptoticClassicalPeterssonNormalizerV1
public import AsymptoticClassicalHeckeFormulaV1
public import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct ComplexConjugate

variable (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ)
variable (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)

include hAB in
/-- The two actual slash-degeneracy directions are adjoint at level p*N. -/
theorem slash_dilation_inner_swap [NeZero (p * N)] (f g : CuspForm (level N) k) :
    inner ℂ ((p : ℂ) ^ (k - 1) • degeneracy N p hp k f)
      (restrict k (level_antitone (dvd_mul_left N p)) g) =
    inner ℂ (restrict k (level_antitone (dvd_mul_left N p)) f)
      ((p : ℂ) ^ (k - 1) • degeneracy N p hp k g) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let I := restrict k (level_antitone (dvd_mul_left N p))
  let c : ℂ := (p : ℂ) ^ (k - 2)
  have hh := inner_slash_normalizer (p * N) k (heckeNormalizerLabel N p hp A B hAB)
    (heckeNormalizerReal N p hp A B hAB)
    (by rw [heckeNormalizerReal_det]; exact_mod_cast hp)
    (heckeNormalizer_action N p hp A B hAB)
    (fun _ ha => heckeNormalizer_conj_mem N p hp A B hAB hN ha)
    (fun _ ha => heckeNormalizer_inv_conj_mem N p hp A B hAB hN ha)
    ((p : ℂ) ^ (k - 1) • degeneracy N p hp k f) (I g)
    (c • I f) ((p : ℂ) ^ (k - 1) • degeneracy N p hp k g)
    (by
      change c • (f : ℍ → ℂ) =
        ((p : ℂ) ^ (k - 1) • (degeneracy N p hp k f : ℍ → ℂ)) ∣[k]
          heckeNormalizerReal N p hp A B hAB
      rw [scaled_degeneracy_coe, slash_dilation_heckeNormalizer])
    (by
      change (p : ℂ) ^ (k - 1) • (degeneracy N p hp k g : ℍ → ℂ) =
        (g : ℍ → ℂ) ∣[k] heckeNormalizerReal N p hp A B hAB
      rw [scaled_degeneracy_coe, slash_heckeNormalizer])
  rw [heckeNormalizerReal_det, inner_smul_left] at hh
  have hc : conj c = c := by simp [c]
  simp only [Complex.ofReal_natCast, hc] at hh
  exact (mul_left_cancel₀ (zpow_ne_zero (k - 2) hpC) hh).symm

include hAB in
/-- The good-prime trace correspondence is symmetric for the actual
 Petersson inner product, derived by a rational normalizer change of variables. -/
theorem dilationTrace_isSymmetric : (dilationTrace N p hp k).IsSymmetric := by
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  have hpair (f g : CuspForm (level N) k) :
      inner ℂ (dilationTrace N p hp k f) g =
        inner ℂ ((p : ℂ) ^ (k - 1) • degeneracy N p hp k f)
          (restrict k (level_antitone (dvd_mul_left N p)) g) := by
    rw [dilationTrace_inner, inner_smul_left]
    simp
  intro f g
  have hr := congrArg (starRingEnd ℂ) (hpair g f)
  simp only [inner_conj_symm] at hr
  exact (hpair f g).trans ((slash_dilation_inner_swap N p hp k A B hAB f g).trans hr.symm)

#print axioms slash_dilation_inner_swap
#print axioms dilationTrace_isSymmetric

end AsymptoticClassicalCusp
