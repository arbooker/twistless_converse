module

public import SmallLevelNormalizedMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelSignedPairs
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- Pair reduction retaining the common scalar of the coherent Fricke laws. -/
theorem pair_reduction (F : ℍ → ℂ) (k : ℤ) (W V C D : GL (Fin 2) ℝ)
    (r : ℝ) (δ : ℂ)
    (hp : W*C*translation (-r)=translation r*V)
    (hn : W*D*translation r=translation (-r)*V)
    (h : (F ∣[k] (W⁻¹*translation r*V))+(F ∣[k] (W⁻¹*translation (-r)*V))=
      δ • ((F ∣[k] translation r)+(F ∣[k] translation (-r)))) :
    (F ∣[k] C)+((F ∣[k] D) ∣[k] translation (2*r))=
      δ • (F+(F ∣[k] translation (2*r))) := by
  have hp' : W⁻¹*translation r*V=C*translation (-r) := by
    rw [mul_assoc,← hp]
    group
  have hn' : W⁻¹*translation (-r)*V=D*translation r := by
    rw [mul_assoc,← hn]
    group
  rw [hp',hn'] at h
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] translation r) h
  rw [det_one_smul _ (translation_det _)] at hh
  have hz : translation 0=1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  simp only [SlashAction.add_slash,← SlashAction.slash_mul,mul_assoc,translation_mul] at hh
  rw [show -r+r=0 by ring,show r+r=2*r by ring,hz,mul_one,SlashAction.slash_one] at hh
  simpa only [SlashAction.slash_mul,add_comm] using hh

theorem inverse_pairs_negative (F : ℍ → ℂ) (k : ℤ) (B C R S : GL (Fin 2) ℝ)
    (h4 : (F ∣[k] B)+((F ∣[k] C) ∣[k] R)= -(F+(F ∣[k] R)))
    (h6 : (F ∣[k] B⁻¹)+((F ∣[k] C⁻¹) ∣[k] S)= -(F+(F ∣[k] S))) :
    ((F ∣[k] B)+F) ∣[k] (R⁻¹*C⁻¹*S*B)=(F ∣[k] B)+F := by
  let v := (F ∣[k] B)+F
  let w := (F ∣[k] C)+F
  have hinv (X : GL (Fin 2) ℝ) : (F ∣[k] X⁻¹)+F=((F ∣[k] X)+F) ∣[k] X⁻¹ := by
    simp only [SlashAction.add_slash,← SlashAction.slash_mul,mul_inv_cancel,
      SlashAction.slash_one,add_comm]
  have hvw : v= -(w ∣[k] R) := by
    dsimp [v,w]
    rw [SlashAction.add_slash]
    linear_combination h4
  have hwv : w= -(v ∣[k] R⁻¹) := by
    have hh := congrArg (fun g : ℍ → ℂ => g ∣[k] R⁻¹) hvw
    simp only [SlashAction.neg_slash,← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hh
    linear_combination hh
  have h6' : ((F ∣[k] B⁻¹)+F)+(((F ∣[k] C⁻¹)+F) ∣[k] S)=0 := by
    rw [SlashAction.add_slash]
    linear_combination h6
  rw [hinv B,hinv C] at h6'
  have hh : (v ∣[k] B⁻¹)= -((w ∣[k] C⁻¹) ∣[k] S) := by
    dsimp [v,w]
    linear_combination h6'
  rw [hwv,SlashAction.neg_slash,SlashAction.neg_slash,neg_neg] at hh
  have h := congrArg (fun g : ℍ → ℂ => g ∣[k] B) hh
  simp only [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one] at h
  exact h.symm

private theorem sub_slash (F G : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) :
    (F-G) ∣[k] g = (F ∣[k] g)-(G ∣[k] g) := by
  simp only [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash]

theorem inverse_pairs_positive (F : ℍ → ℂ) (k : ℤ) (B C R S : GL (Fin 2) ℝ)
    (h4 : (F ∣[k] B)+((F ∣[k] C) ∣[k] R)=F+(F ∣[k] R))
    (h6 : (F ∣[k] B⁻¹)+((F ∣[k] C⁻¹) ∣[k] S)=F+(F ∣[k] S)) :
    ((F ∣[k] B)-F) ∣[k] (R⁻¹*C⁻¹*S*B)=(F ∣[k] B)-F := by
  let v := (F ∣[k] B)-F
  let w := (F ∣[k] C)-F
  have hinv (X : GL (Fin 2) ℝ) : (F ∣[k] X⁻¹)-F= -(((F ∣[k] X)-F) ∣[k] X⁻¹) := by
    simp only [sub_slash,← SlashAction.slash_mul,mul_inv_cancel,
      SlashAction.slash_one,neg_sub]
  have hvw : v= -(w ∣[k] R) := by
    dsimp [v,w]
    rw [sub_slash]
    linear_combination h4
  have hwv : w= -(v ∣[k] R⁻¹) := by
    have hh := congrArg (fun g : ℍ → ℂ => g ∣[k] R⁻¹) hvw
    simp only [SlashAction.neg_slash,← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hh
    linear_combination hh
  have h6' : ((F ∣[k] B⁻¹)-F)+(((F ∣[k] C⁻¹)-F) ∣[k] S)=0 := by
    rw [sub_slash]
    linear_combination h6
  rw [hinv B,hinv C,SlashAction.neg_slash] at h6'
  have hh : (v ∣[k] B⁻¹)= -((w ∣[k] C⁻¹) ∣[k] S) := by
    dsimp [v,w]
    linear_combination -h6'
  rw [hwv,SlashAction.neg_slash,SlashAction.neg_slash,neg_neg] at hh
  have h := congrArg (fun g : ℍ → ℂ => g ∣[k] B) hh
  simp only [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one] at h
  exact h.symm

#print axioms inverse_pairs_positive

/-- Both bad-prime signs give the same hyperbolic invariance of the defect. -/
theorem inverse_pairs (F : ℍ → ℂ) (k : ℤ) (B C R S : GL (Fin 2) ℝ)
    (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (h4 : (F ∣[k] B)+((F ∣[k] C) ∣[k] R)=δ • (F+(F ∣[k] R)))
    (h6 : (F ∣[k] B⁻¹)+((F ∣[k] C⁻¹) ∣[k] S)=δ • (F+(F ∣[k] S))) :
    ((F ∣[k] B)-δ • F) ∣[k] (R⁻¹*C⁻¹*S*B)=(F ∣[k] B)-δ • F := by
  rcases hδ with rfl|rfl
  · simp only [one_smul] at h4 h6 ⊢
    exact inverse_pairs_positive F k B C R S h4 h6
  · simp only [neg_one_smul,sub_neg_eq_add] at h4 h6 ⊢
    exact inverse_pairs_negative F k B C R S h4 h6

#print axioms pair_reduction
#print axioms inverse_pairs
end SmallLevelSignedPairs

namespace QuantitativeArithmeticSmallLevelTwentyFivePairs
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem inverse_pairs (F : ℍ → ℂ) (k : ℤ) (B C R S : GL (Fin 2) ℝ)
    (h4 : (F ∣[k] B)+((F ∣[k] C) ∣[k] R)=F+(F ∣[k] R))
    (h6 : (F ∣[k] B⁻¹)+((F ∣[k] C⁻¹) ∣[k] S)=F+(F ∣[k] S)) :
    ((F ∣[k] B)-F) ∣[k] (R⁻¹*C⁻¹*S*B)=(F ∣[k] B)-F := by
  exact SmallLevelSignedPairs.inverse_pairs_positive F k B C R S h4 h6

#print axioms inverse_pairs
end QuantitativeArithmeticSmallLevelTwentyFivePairs
