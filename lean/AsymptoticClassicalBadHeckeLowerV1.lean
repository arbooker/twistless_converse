module

public import AsymptoticClassicalBadHeckeV1
public import AsymptoticClassicalOldIntersectionGroupsV1
public import AsymptoticClassicalTraceTranslateV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups Pointwise

/-- At the lower target level the conjugated source has the same upper-entry
congruence condition as the U_p correspondence at that target. -/
theorem upperDilationLevel_lower_mem (M p : ℕ) (hp : 0 < p) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 M) :
    SpecialLinearGroup.mapGL ℝ A ∈ upperDilationLevel (p * M) p hp ↔ (p : ℤ) ∣ A 0 1 := by
  constructor
  · rintro ⟨_, ⟨B, _, rfl⟩, he⟩
    have hi : upperDilationReal p hp * SpecialLinearGroup.mapGL ℝ A =
        SpecialLinearGroup.mapGL ℝ B * upperDilationReal p hp := by
      rw [← he]
      change upperDilationReal p hp * ((upperDilationReal p hp)⁻¹ *
        SpecialLinearGroup.mapGL ℝ B * ((upperDilationReal p hp)⁻¹)⁻¹) = _
      group
    have hb := congrArg (fun g : GL (Fin 2) ℝ => g.val 0 1) hi
    have hb' : (A 0 1 : ℝ) = (p : ℝ) * (B 0 1 : ℝ) := by
      simpa [upperDilationReal, upperDilationGL, GeneralLinearGroup.map,
        GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.mapGL,
        Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using hb
    exact ⟨B 0 1, by exact_mod_cast hb'⟩
  · rintro ⟨b, hb⟩
    have hB : upperDilationConjugate p A b hb ∈ CongruenceSubgroup.Gamma0 (p * M) := by
      obtain ⟨c, hc⟩ := (gamma0_mem_dvd M A).mp hA
      rw [gamma0_mem_dvd]
      refine ⟨c, ?_⟩
      change (p : ℤ) * A 1 0 = ((p * M : ℕ) : ℤ) * c
      rw [hc, Nat.cast_mul, mul_assoc]
    refine ⟨SpecialLinearGroup.mapGL ℝ (upperDilationConjugate p A b hb),
      ⟨_, hB, rfl⟩, ?_⟩
    change (upperDilationReal p hp)⁻¹ * _ * ((upperDilationReal p hp)⁻¹)⁻¹ = _
    rw [inv_inv, mul_assoc, ← upperDilation_intertwine p hp A b hb, inv_mul_cancel_left]

theorem upperDilationLevel_lower_subgroup (M p : ℕ) (hp : 0 < p) :
    (upperDilationLevel (p * M) p hp).subgroupOf (level M) =
      (upperDilationLevel M p hp).subgroupOf (level M) := by
  ext g
  obtain ⟨A, hA, he⟩ := g.property
  change g.val ∈ upperDilationLevel (p * M) p hp ↔ g.val ∈ upperDilationLevel M p hp
  rw [← he, upperDilationLevel_lower_mem M p hp A hA, upperDilationLevel_mem_iff M p hp A hA]

/-- The lower trace has the same p translation representatives at a repeated prime. -/
def upperLowerCosetEquiv (M p : ℕ) (hp : p.Prime) (hpM : p ∣ M) :
    Fin p ≃ level M ⧸ (upperDilationLevel (p * M) p hp.pos).subgroupOf (level M) :=
  (upperCosetEquiv M p hp hpM).trans
    (Subgroup.quotientEquivOfEq (upperDilationLevel_lower_subgroup M p hp.pos).symm)

theorem upperLowerCosetEquiv_mk (M p : ℕ) (hp : p.Prime) (hpM : p ∣ M) (a : Fin p) :
    upperLowerCosetEquiv M p hp hpM a = QuotientGroup.mk (upperRepresentative M a.val) := by
  exact Subgroup.quotientEquivOfEq_mk
    (upperDilationLevel_lower_subgroup M p hp.pos).symm (upperRepresentative M a.val)

/-- The two diagonal correspondences compose to a central scalar. -/
theorem dilation_upper_product (p : ℕ) (hp : 0 < p) :
    dilationReal p hp * upperDilationReal p hp =
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne')) := by
  apply Units.ext
  change (dilationReal p hp).val * (upperDilationReal p hp).val =
    Matrix.diagonal (fun _ : Fin 2 => (p : ℝ))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationReal, dilationGL, upperDilationReal, upperDilationGL,
      GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower degeneracy group translates back to the ordinary lower level. -/
theorem upper_translate_dilationLevel (M p : ℕ) (hp : 0 < p) :
    toConjAct (upperDilationReal p hp)⁻¹ • dilationLevel M p hp = level M := by
  have he (a : GL (Fin 2) ℝ) :
      toConjAct (upperDilationReal p hp)⁻¹ •
        (toConjAct (dilationReal p hp)⁻¹ • a) = a := by
    rw [← mul_smul, ← map_mul, ← _root_.mul_inv_rev, dilation_upper_product]
    change (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) _) )⁻¹ * a *
      ((GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) _) )⁻¹)⁻¹ = a
    rw [inv_inv]
    have hc := GeneralLinearGroup.scalar_commute (Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne')) a
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  ext a
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    change toConjAct (upperDilationReal p hp)⁻¹ •
      (toConjAct (dilationReal p hp)⁻¹ • b) ∈ level M
    rw [he]
    exact hb
  · intro ha
    exact ⟨_, ⟨a, ha, rfl⟩, he a⟩

/-- A representative-compatible coset parameterization gives the literal upper-branch trace. -/
theorem upperTrace_coset_sum (N M p : ℕ) [NeZero N] [NeZero M] (hp : 0 < p)
    (e : Fin p ≃ level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M))
    (he : ∀ a, e a = QuotientGroup.mk (upperRepresentative M a.val))
    (k : ℤ) (f : CuspForm (level N) k) :
    (arithmeticTrace (upperDilationLevel N p hp) (level M) k
      (CuspForm.translate f (upperDilationReal p hp)) : ℍ → ℂ) =
      ∑ a : Fin p, (f : ℍ → ℂ) ∣[k]
        triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp) := by
  classical
  let : (upperDilationLevel N p hp).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel N p hp)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M))
  change (∑ q : level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M),
    SlashInvariantForm.quotientFunc (CuspForm.translate f (upperDilationReal p hp)) q) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [he a]
  change SlashInvariantForm.quotientFunc (CuspForm.translate f (upperDilationReal p hp))
    (QuotientGroup.mk (upperRepresentative M a.val)) = _
  rw [SlashInvariantForm.quotientFunc_mk]
  change ((f : ℍ → ℂ) ∣[k] upperDilationReal p hp) ∣[k]
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


#print axioms upperTrace_coset_sum
#print axioms upperDilationLevel_lower_mem
#print axioms upperDilationLevel_lower_subgroup
#print axioms upperLowerCosetEquiv_mk
#print axioms dilation_upper_product
#print axioms upper_translate_dilationLevel
end AsymptoticClassicalCusp
