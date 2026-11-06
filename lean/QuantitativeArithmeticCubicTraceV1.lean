module
public import SmallLevelNormalizedMatricesV1
public import Mathlib.Tactic.Group
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticCubicTrace
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem cubic (F : ℍ → ℂ) (k : ℤ) (R : GL (Fin 2) ℝ)
    (h : F+(F ∣[k] R)+((F ∣[k] R) ∣[k] R)=0) :
    ((F ∣[k] R) ∣[k] R) ∣[k] R=F := by
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] R) h
  simp only [SlashAction.add_slash,SlashAction.zero_slash] at hh
  funext z
  have h0 := congrFun h z
  have h1 := congrFun hh z
  simp only [Pi.add_apply,Pi.zero_apply] at h0 h1
  linear_combination h1-h0

theorem inverse_trace (F : ℍ → ℂ) (k : ℤ) (R : GL (Fin 2) ℝ)
    (h : F+(F ∣[k] R)+((F ∣[k] R) ∣[k] R)=0) :
    F+(F ∣[k] R⁻¹)+((F ∣[k] R⁻¹) ∣[k] R⁻¹)=0 := by
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[k] R⁻¹) ∣[k] R⁻¹) h
  simpa only [SlashAction.add_slash,SlashAction.zero_slash,← SlashAction.slash_mul,
    mul_assoc,mul_inv_cancel,one_mul,mul_one,SlashAction.slash_one,add_assoc,add_comm,add_left_comm] using hh

theorem inverse_square (F : ℍ → ℂ) (k : ℤ) (S : GL (Fin 2) ℝ)
    (h : F+(F ∣[k] S)+((F ∣[k] S) ∣[k] S)=0) :
    (F ∣[k] S⁻¹) ∣[k] S⁻¹=F ∣[k] S := by
  have hh := congrArg (fun G : ℍ → ℂ => (G ∣[k] S⁻¹) ∣[k] S⁻¹) (cubic F k S h)
  simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one] using hh.symm

theorem conjugate_trace (F : ℍ → ℂ) (k : ℤ) (R S W : GL (Fin 2) ℝ) (χ : ℂ)
    (hdet : (GeneralLinearGroup.det R:ℝ)=1)
    (hR : F+(F ∣[k] R)+((F ∣[k] R) ∣[k] R)=0)
    (hW : F ∣[k] W=χ • F) (he : S*W=W*R) :
    F+(F ∣[k] S)+((F ∣[k] S) ∣[k] S)=0 := by
  have he2 : S*S*W=W*R*R := by
    rw [mul_assoc,he,← mul_assoc,he,mul_assoc]
  have hh : (F+(F ∣[k] S)+((F ∣[k] S) ∣[k] S)) ∣[k] W=0 := by
    simp only [SlashAction.add_slash,← SlashAction.slash_mul,he,he2]
    simp only [SlashAction.slash_mul,hW,det_one_smul R hdet]
    rw [← smul_add,← smul_add,hR,smul_zero]
  exact (SlashAction.slash_eq_zero_iff k W _).mp hh

/-- The odd-modulus transformation gives the commutator after the lower
cubic trace has been imposed, without assuming invariance of translates. -/
theorem commutator (F : ℍ → ℂ) (k : ℤ) (R S : GL (Fin 2) ℝ)
    (hS : F+(F ∣[k] S)+((F ∣[k] S) ∣[k] S)=0)
    (he : F ∣[k] (S⁻¹*S⁻¹*R*S⁻¹*R⁻¹)=F) :
    F ∣[k] (S*R)=F ∣[k] (R*S) := by
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] (R*S)) he
  have hm : (S⁻¹*S⁻¹*R*S⁻¹*R⁻¹)*(R*S)=S⁻¹*S⁻¹*R := by group
  rw [← SlashAction.slash_mul,hm] at hh
  simpa only [SlashAction.slash_mul,inverse_square F k S hS] using hh

#print axioms cubic
#print axioms conjugate_trace
#print axioms commutator
end QuantitativeArithmeticCubicTrace
