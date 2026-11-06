module

public import AsymptoticGeneratorDetectionV1
public import Mathlib.GroupTheory.Schreier
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticIntegralSubgroup AsymptoticFreshMatrices AsymptoticRationalGroup
open AsymptoticDecodedCongruence AsymptoticOrbitDecode
open scoped MatrixGroups

theorem gamma0_finitely_generated (N : ℕ) [NeZero N] : (CongruenceSubgroup.Gamma0 N).FG := by
  let : Group.FG SL(2,ℤ) := Group.fg_iff.mpr
    ⟨{ModularGroup.S,ModularGroup.T},SpecialLinearGroup.SL2Z_generators,Set.toFinite _⟩
  exact (Group.fg_iff_subgroup_fg _).mp inferInstance

theorem exists_generators (N : ℕ) [NeZero N] :
    ∃ S : Finset SL(2,ℤ),Subgroup.closure (S:Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N :=
  by
    obtain ⟨S,hS,hfin⟩ := (Subgroup.fg_iff _).mp (gamma0_finitely_generated N)
    exact ⟨hfin.toFinset,by simpa only [Set.Finite.coe_toFinset] using hS⟩

/-- Matrices with zero lower-left entry contribute only integral
translation relations after passing to the projective group. -/
theorem triangular_label (γ : SL(2,ℤ)) (hc : γ 1 0=0) :
    ∃ u : ℤ,integralLabel γ=translationLabel (u:ℚ) := by
  have hd : γ 0 0*γ 1 1=1 := by
    have h := γ.property
    rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at h
    exact h
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hd with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · refine ⟨γ 0 1,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change rationalMap (rationalGL γ)=rationalMap (AsymptoticMobiusFold.translation (γ 0 1:ℚ))
    congr 1
    apply Units.ext
    change γ.val.map (fun z : ℤ => (z:ℚ))=(AsymptoticMobiusFold.translation (γ 0 1:ℚ)).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply,ha,hd,hc,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero]
  · refine ⟨-γ 0 1,?_⟩
    have he : rationalGL γ=AsymptoticMobiusFold.translation ((-γ 0 1:ℤ):ℚ)*
        GeneralLinearGroup.scalar (Fin 2) (-1:ℚˣ) := by
      apply Units.ext
      change γ.val.map (fun z : ℤ => (z:ℚ))=
        (AsymptoticMobiusFold.translation ((-γ 0 1:ℤ):ℚ)).val*
          (GeneralLinearGroup.scalar (Fin 2) (-1:ℚˣ)).val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.map_apply,ha,hd,hc,AsymptoticMobiusFold.translation,GeneralLinearGroup.mkOfDetNeZero,
          GeneralLinearGroup.scalar,Matrix.scalar,Matrix.mul_apply,Fin.sum_univ_two]
    apply Subtype.ext
    apply Subtype.ext
    change rationalMap (rationalGL γ)=rationalMap (AsymptoticMobiusFold.translation ((-γ 0 1:ℤ):ℚ))
    rw [he,map_mul,rationalMap_scalar,mul_one]

/-- It suffices to detect the finitely many generators with nonzero
lower-left entry. The remaining generators act by periodicity. -/
theorem gamma0_invariance_of_generators (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S:Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (F : AsymptoticRationalGroup.Group → ℂ)
    (hp : ∀ u : ℤ,translationLabel (u:ℚ)∈invariantSubgroup F)
    (hgen : ∀ γ∈S,γ 1 0≠0 → integralLabel γ∈invariantSubgroup F) :
    ∀ γ∈CongruenceSubgroup.Gamma0 N,integralLabel γ∈invariantSubgroup F := by
  have hle : CongruenceSubgroup.Gamma0 N≤(invariantSubgroup F).comap integralLabel := by
    rw [← hS,Subgroup.closure_le]
    intro γ hγ
    by_cases hc : γ 1 0=0
    · obtain ⟨u,hu⟩ := triangular_label γ hc
      change integralLabel γ∈invariantSubgroup F
      rw [hu]
      exact hp u
    · exact hgen γ hγ hc
  exact fun γ hγ => hle hγ

#print axioms gamma0_finitely_generated
#print axioms exists_generators
#print axioms triangular_label
#print axioms gamma0_invariance_of_generators

end AsymptoticCongruenceLabels
