module

public import QuantitativeMaassHeckeTreeRawV1
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix
open scoped Matrix MatrixGroups BigOperators

namespace QuantitativeMaass
namespace HeckeUpper

/-- The literal projective identity coset: a nonzero rational scalar times
an actual integral level-N determinant-one matrix. -/
def projectiveGamma (N : ℕ) (M : HeckeUpper) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N ∧
    M.matrix.map (Int.castRingHom ℚ) = c • γ.val.map (Int.castRingHom ℚ)

/-- For a nonsingular upper-triangular integral matrix the projective
identity condition is exactly the integer-translation test, at every level. -/
theorem projectiveGamma_iff_translation (N : ℕ) (M : HeckeUpper) (hdet : M.det ≠ 0) :
    projectiveGamma N M ↔ M.translation := by
  constructor
  · rintro ⟨c,hc,γ,_,he⟩
    have he00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 0) he
    have he01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 1) he
    have he10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 1 0) he
    have he11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 1 1) he
    change (M.a : ℚ) = c * (γ.val 0 0 : ℚ) at he00
    change (M.b : ℚ) = c * (γ.val 0 1 : ℚ) at he01
    change (0 : ℚ) = c * (γ.val 1 0 : ℚ) at he10
    change (M.d : ℚ) = c * (γ.val 1 1 : ℚ) at he11
    have h10q : (γ.val 1 0 : ℚ) = 0 := (mul_eq_zero.mp he10.symm).resolve_left hc
    have h10 : γ.val 1 0 = 0 := by exact_mod_cast h10q
    have hγdet : γ.val 0 0 * γ.val 1 1 = 1 := by
      have hh := γ.property
      simpa only [Matrix.det_fin_two, h10, mul_zero, sub_zero] using hh
    have hdiag : γ.val 0 0 = γ.val 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hγdet with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;>
        rw [h0,h1]
    have hsq : (γ.val 1 1)^2 = 1 := by simpa only [hdiag, pow_two] using hγdet
    have ha : M.a = M.d := by
      apply Int.cast_injective (α := ℚ)
      rw [he00, he11, hdiag]
    refine ⟨ha, γ.val 0 1 * γ.val 1 1, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [he01, he11]
    have hsqQ : (γ.val 1 1 : ℚ)^2 = 1 := by exact_mod_cast hsq
    calc
      c * (γ.val 0 1 : ℚ) = c * (γ.val 0 1 : ℚ) * (γ.val 1 1 : ℚ)^2 := by rw [hsqQ, mul_one]
      _ = _ := by ring
  · rintro ⟨ha,n,hb⟩
    have hd : M.d ≠ 0 := by
      intro h
      exact hdet (by simp [det, h])
    let γ : SL(2, ℤ) := ⟨!![1,n;0,1], by simp [Matrix.det_fin_two]⟩
    refine ⟨(M.d : ℚ), by exact_mod_cast hd, γ, ?_, ?_⟩
    · apply CongruenceSubgroup.Gamma0_mem.mpr
      simp [γ]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matrix, γ, ha, hb, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

attribute [local instance] Classical.propDecidable

/-- Count the identity terms in the original p+1 representative expansion,
with the endpoint tested in the actual projective Gamma0(N) coset. -/
def cosetWalks (N p : ℕ) [Fact p.Prime] : ℕ → HeckeUpper → ℕ
  | 0, M => if projectiveGamma N M then 1 else 0
  | n+1, M => ∑ j : Option (ZMod p), cosetWalks N p n (left p j M)

theorem cosetWalks_eq_rawWalks (N p n : ℕ) [Fact p.Prime] (M : HeckeUpper)
    (hdet : M.det ≠ 0) : cosetWalks N p n M = rawWalks p n M := by
  induction n generalizing M with
  | zero => simp only [cosetWalks, rawWalks, projectiveGamma_iff_translation N M hdet]
  | succ n ih =>
    simp only [cosetWalks, rawWalks]
    apply Finset.sum_congr rfl
    intro j _
    apply ih
    rw [left_det]
    apply mul_ne_zero _ hdet
    exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Exact identity coefficient of the unnormalized p+1 branch expansion,
proved from integral matrices and the actual congruence subgroup. -/
theorem cosetWalks_root_eq_tree (N p n : ℕ) [Fact p.Prime] :
    cosetWalks N p n root = treeWalkCount (p+1) n 0 := by
  rw [cosetWalks_eq_rawWalks N p n root (by simp [root_det]), rawWalks_root_eq_tree]

#print axioms projectiveGamma_iff_translation
#print axioms cosetWalks_root_eq_tree

end HeckeUpper
end QuantitativeMaass
