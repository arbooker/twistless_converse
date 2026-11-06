module

public import AsymptoticClassicalLocalAtkinOperatorV1
public import AsymptoticClassicalHeckeTraceSumV1
public import AsymptoticClassicalBadHeckeRepeatedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane Matrix ConjAct AsymptoticAtkinLehner AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups Pointwise

/-- Replacing equal groups and equal cusp functions leaves the literal trace unchanged. -/
theorem trace_coe_congr {G G' H H' : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [G'.IsFiniteRelIndex H'] (k : ℤ) (hG : G = G') (hH : H = H')
    (f : CuspForm G k) (g : CuspForm G' k) (hfg : (f : ℍ → ℂ) = g) :
    (CuspForm.trace H f : ℍ → ℂ) = (CuspForm.trace H' g : ℍ → ℂ) := by
  subst G'
  subst H'
  have he : f = g := DFunLike.coe_injective hfg
  subst g
  rfl

variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

/-- The second old trace becomes the ordinary trace after local Atkin. -/
theorem localAtkin_trace_zero [NeZero M] (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hf : let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p hp) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
    arithmeticTrace (level (p * M)) (level M) k (localAtkinOperator M p hp A B hAB k f) = 0 := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
  dsimp only
  let G := level (p * M)
  let H := dilationLevel M p hp
  let V := localAtkinReal M p hp A B hAB
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let := conjugate_finiteRelIndex G H V
  let : G.IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  have hzero : (CuspForm.trace H f : ℍ → ℂ) = 0 :=
    congrArg (fun h : CuspForm H k => (h : ℍ → ℂ)) hf
  have ht := trace_translate G H V k f
  rw [hzero, SlashAction.zero_slash] at ht
  have he := trace_coe_congr k (localAtkinReal_normalizes M p hp A B hAB)
    (localAtkinReal_oldGroup_back M p hp A B hAB)
    (CuspForm.translate f V) (localAtkinOperator M p hp A B hAB k f) rfl
  apply DFunLike.coe_injective
  exact he.symm.trans ht

/-- Local Atkin times an upper Hecke branch is p times an ordinary trace representative. -/
theorem localAtkin_upper_branch (a : ℤ) :
    localAtkinReal M p hp A B hAB * triangularGL 1 a p (by norm_num) (by exact_mod_cast hp) =
      SpecialLinearGroup.mapGL ℝ (traceSL M p A B hAB a) * positiveScalarReal p hp := by
  apply Units.ext
  change (localAtkinReal M p hp A B hAB).val *
      (triangularGL 1 a p (by norm_num) (by exact_mod_cast hp)).val =
    (traceSL M p A B hAB a).val.map (fun z : ℤ => (z : ℝ)) * (positiveScalarReal p hp).val
  rw [localAtkinReal_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularGL, positiveScalarReal, traceSL, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- The actual I + W_p U_p trace identity, with Mathlib's exact weight normalization. -/
theorem upperTrace_localAtkin [NeZero M] [Fact p.Prime] (hM : 0 < M) (hpM : ¬ p ∣ M)
    (k : ℤ) (f : CuspForm (level (p * M)) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
    (upperTrace (p * M) p hp k (localAtkinOperator M p hp A B hAB k f) : ℍ → ℂ) =
      (p : ℂ) ^ (k - 2) • ((arithmeticTrace (level (p * M)) (level M) k f : ℍ → ℂ) - f) := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
  dsimp only
  rw [upperTrace_bad_slash (p * M) p (Fact.out : p.Prime) (Nat.dvd_mul_right p M),
    arithmeticTrace_prime_sum M p hM hpM A B hAB k f]
  simp only [add_sub_cancel_left]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hb := localAtkin_upper_branch M p hp A B hAB (a.val : ℤ)
  simp only [Int.cast_natCast] at hb
  rw [localAtkinOperator_coe, ← SlashAction.slash_mul, hb,
    SlashAction.slash_mul, slash_positiveScalarReal]
  rfl

#print axioms trace_coe_congr
#print axioms localAtkin_trace_zero
#print axioms localAtkin_upper_branch
#print axioms upperTrace_localAtkin
end AsymptoticClassicalCusp
