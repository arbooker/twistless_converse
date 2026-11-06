module

public import SmallLevelTwentyOneChiFiveMatricesV1
public import SmallLevelTwentyOneChiFiveTheoryV4
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveGroup
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFive
open scoped MatrixGroups ModularForm

theorem separated_second_pair {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*quadraticFourier k f (-1/((525:ℂ)*z))) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] C)-SmallLevelOriginal.fourierFunction k f)
        ∣[(k:ℤ)] translation (2/5)+
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] D)-SmallLevelOriginal.fourierFunction k f)
        ∣[(k:ℤ)] translation (-2/5)=0 := by
  have h := second_pair_slash ε hlaw hquad
  have hp : (fricke 21 (by decide))⁻¹*translation (2/5)*fricke 525 (by decide)=
      SpecialLinearGroup.mapGL ℝ C*translation (2/5) := by
    rw [mul_assoc,← C_branch]
    group
  have hn : (fricke 21 (by decide))⁻¹*translation (-2/5)*fricke 525 (by decide)=
      SpecialLinearGroup.mapGL ℝ D*translation (-2/5) := by
    rw [mul_assoc,← D_branch]
    group
  rw [hp,hn,SlashAction.slash_mul,SlashAction.slash_mul] at h
  simp only [SmallLevelEleven.sub_slash]
  linear_combination h

private theorem translation_zero : translation 0=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]

private theorem translation_T : SpecialLinearGroup.mapGL ℝ ModularGroup.T=translation 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ModularGroup.T,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]

/-- The separated second pair and the already known E,T,U symmetries force
the C-defect to be invariant under the explicit trace4/5 elliptic matrix. -/
theorem defect_elliptic (F : ℍ → ℂ) (k : ℤ)
    (hE : F ∣[k] E=F) (hT : F ∣[k] ModularGroup.T=F)
    (hU : F ∣[k] lower 21=F)
    (hp : ((F ∣[k] C)-F) ∣[k] translation (2/5)+
      ((F ∣[k] D)-F) ∣[k] translation (-2/5)=0) :
    ((F ∣[k] C)-F) ∣[k] SmallLevelTwentyOneChiFiveRigidity.ellipticReal=(F ∣[k] C)-F := by
  let X := SpecialLinearGroup.mapGL ℝ C⁻¹*SpecialLinearGroup.mapGL ℝ E*
    SpecialLinearGroup.mapGL ℝ ModularGroup.T
  have hD : F ∣[k] D=F ∣[k] X := by
    rw [D_factor]
    simp only [SlashAction.slash_mul,hU,hE]
    simp only [X,SlashAction.slash_mul]
    rfl
  have hCX : SpecialLinearGroup.mapGL ℝ C*X=
      SpecialLinearGroup.mapGL ℝ E*SpecialLinearGroup.mapGL ℝ ModularGroup.T := by
    dsimp [X]
    rw [map_inv]
    group
  have hY : F ∣[k] (SpecialLinearGroup.mapGL ℝ E*SpecialLinearGroup.mapGL ℝ ModularGroup.T)=F := by
    rw [SlashAction.slash_mul]
    change (F ∣[k] E) ∣[k] ModularGroup.T=F
    rw [hE,hT]
  have hd : (F ∣[k] D)-F= -(((F ∣[k] C)-F) ∣[k] X) := by
    change (F ∣[k] D)-F= -(((F ∣[k] SpecialLinearGroup.mapGL ℝ C)-F) ∣[k] X)
    rw [SmallLevelEleven.sub_slash,← SlashAction.slash_mul,hCX,hY,hD]
    abel
  rw [hd,SlashAction.neg_slash] at hp
  have hh := congrArg (fun H : ℍ → ℂ => H ∣[k] translation (-2/5)) hp
  simp only [SlashAction.add_slash,SlashAction.neg_slash,SlashAction.zero_slash,
    ← SlashAction.slash_mul,mul_assoc,translation_mul] at hh
  norm_num only [show (2/5:ℝ)+ -2/5=0 by ring,
    show (-2/5:ℝ)+ -2/5= -4/5 by ring,translation_zero,mul_one,SlashAction.slash_one] at hh
  have hx : X*translation (-4/5)=SmallLevelTwentyOneChiFiveRigidity.ellipticReal := by
    rw [elliptic_factor]
    dsimp [X]
    rw [translation_T,mul_assoc,translation_mul]
    norm_num
  simp only [neg_div] at hx
  rw [hx] at hh
  linear_combination -hh

#print axioms separated_second_pair
#print axioms defect_elliptic
end SmallLevelTwentyOneChiFiveGroup
