module
public import AsymptoticClassicalBadHeckeCosetsV1
public import AsymptoticClassicalEigenCoefficientsV1
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane Matrix AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

/-- The standard trace correspondence in the diag(1,p) direction. -/
def upperTrace (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ) :
    CuspForm (level N) k →ₗ[ℂ] CuspForm (level N) k :=
  (arithmeticTrace (upperDilationLevel N p hp) (level N) k).comp
    (translateLinear (level N) k (upperDilationReal p hp)
      (by rw [upperDilationReal_det]; exact_mod_cast hp))

theorem upperDilation_translation (p : ℕ) (hp : 0 < p) (a : ℤ) :
    upperDilationReal p hp * SpecialLinearGroup.mapGL ℝ (upperSL a) =
      triangularGL 1 a p (by norm_num) (by exact_mod_cast hp) := by
  apply Units.ext
  change (upperDilationReal p hp).val * (upperSL a).val.map (fun z : ℤ => (z : ℝ)) =
    (triangularGL 1 a p (by norm_num) (by exact_mod_cast hp)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperDilationReal, upperDilationGL, upperSL, AsymptoticFreshCRT.upper,
      triangularGL, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- At a bad prime the genuine trace consists of exactly the p upper branches. -/
theorem upperTrace_bad_slash (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (k : ℤ) (f : CuspForm (level N) k) :
    (upperTrace N p hp.pos k f : ℍ → ℂ) =
      ∑ a : Fin p, (f : ℍ → ℂ) ∣[k]
        triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp.pos) := by
  classical
  let : (upperDilationLevel N p hp.pos).IsFiniteRelIndex (level N) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel N p hp.pos)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).symm).1
  let := Fintype.ofFinite (level N ⧸ (upperDilationLevel N p hp.pos).subgroupOf (level N))
  let e := upperCosetEquiv N p hp hpN
  change (∑ q : level N ⧸ (upperDilationLevel N p hp.pos).subgroupOf (level N),
    SlashInvariantForm.quotientFunc (CuspForm.translate f (upperDilationReal p hp.pos)) q) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  change SlashInvariantForm.quotientFunc (CuspForm.translate f (upperDilationReal p hp.pos))
    (QuotientGroup.mk (upperRepresentative N a.val)) = _
  rw [SlashInvariantForm.quotientFunc_mk]
  change ((f : ℍ → ℂ) ∣[k] upperDilationReal p hp.pos) ∣[k]
    (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ = _
  rw [← SlashAction.slash_mul]
  have he : (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ =
      SpecialLinearGroup.mapGL ℝ (upperSL a.val) := by
    rw [← map_inv]
    congr 1
    apply Subtype.ext
    change Matrix.adjugate !![1, -(a.val : ℤ); 0, 1] = !![1, (a.val : ℤ); 0, 1]
    simp [Matrix.adjugate_fin_two]
  rw [he, upperDilation_translation]
  rfl

theorem upperTrace_bad_apply (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (k : ℤ) (f : CuspForm (level N) k) (z : ℍ) :
    upperTrace N p hp.pos k f z = heckeAverage p hp.pos f z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ht : triangularFactor 1 p k = (p : ℂ)⁻¹ := by
    simp only [triangularFactor, one_mul, Complex.ofReal_natCast]
    rw [← zpow_add₀ hpC, show k - 1 + -k = -1 by omega, _root_.zpow_neg_one]
  have hf := congrFun (upperTrace_bad_slash N p hp hpN k f) z
  simp only [Finset.sum_apply, slash_triangular, ht] at hf
  rw [← Finset.mul_sum] at hf
  exact hf

/-- The Fourier law of the actual bad-prime U_p operator. -/
theorem coeff_upperTrace_bad (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (k : ℤ) (f : CuspForm (level N) k) (n : ℕ) :
    cuspCoefficient N k n (upperTrace N p hp.pos k f) = cuspCoefficient N k (p * n) f := by
  change (qExpansion 1 (upperTrace N p hp.pos k f)).coeff n = _
  symm
  apply ModularFormClass.qExpansion_coeff_unique
    (f := upperTrace N p hp.pos k f)
    (c := fun n => cuspCoefficient N k (p * n) f)
    zero_lt_one (level_one_period N) (m := n)
  intro z
  rw [upperTrace_bad_apply N p hp hpN]
  exact hasSum_heckeAverage p hp.pos f (fun m => cuspCoefficient N k m f)
    (fun z => ModularForm.hasSum_qExpansion (f := f) zero_lt_one (level_one_period N) z) z

#print axioms upperDilation_translation
#print axioms upperTrace_bad_slash
#print axioms upperTrace_bad_apply
#print axioms coeff_upperTrace_bad
end AsymptoticClassicalCusp
