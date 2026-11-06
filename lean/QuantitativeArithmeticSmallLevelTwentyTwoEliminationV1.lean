module

public import QuantitativeArithmeticSmallLevelTwentyTwoFinishBranchesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

private theorem W_det : (GeneralLinearGroup.det W:ℝ)=1 := fricke_det _ _

private theorem sub_slash (F G : ℍ→ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (F-G) ∣[k] M=F ∣[k] M-G ∣[k] M := by
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]

/-- The first branch relation reconstructs the P defect from the auxiliary defect. -/
theorem h_from_first {k : ℤ} (u h : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hfirst : δ • (u ∣[k] translation (-2/3))=
      u ∣[k] (translation (-1)*M 1)+(δ*η) • (h ∣[k] (W*M 0))) :
    h=η • (u ∣[k] J1)-(δ*η) • (u ∣[k] J2) := by
  let v : GL (Fin 2) ℝ := (M 0)⁻¹*W⁻¹
  have hvd : (GeneralLinearGroup.det v:ℝ)=1 := by
    change (GeneralLinearGroup.det ((M 0)⁻¹*W⁻¹):ℝ)=1
    rw [map_mul,Units.val_mul,det_one_inv _ (M_det 0),det_one_inv _ W_det]
    norm_num
  have he:=congrArg (fun g : ℍ→ℂ => g ∣[k] v) hfirst
  rw [SlashAction.add_slash,det_one_smul _ hvd,det_one_smul _ hvd,
    ← SlashAction.slash_mul,← SlashAction.slash_mul,← SlashAction.slash_mul] at he
  have hj1 : translation (-2/3)*v=J1 := by simp only [v,J1,mul_assoc]
  have hj2 : translation (-1)*M 1*v=J2 := by simp only [v,J2,mul_assoc]
  have hc : W*M 0*v=1 := by simp [v,mul_assoc]
  rw [hj1,hj2,hc,SlashAction.slash_one] at he
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;>
    simp only [one_smul,neg_one_smul,one_mul,mul_one,neg_mul,neg_neg] at he ⊢ <;>
      first | linear_combination he | linear_combination -he

/-- Exact substitution of the first branch equation into the second gives
precisely the four-term relation used by the two elliptic matrices. -/
theorem four_term_of_two_relations {k : ℤ} (u h : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hfirst : δ • (u ∣[k] translation (-2/3))=
      u ∣[k] (translation (-1)*M 1)+(δ*η) • (h ∣[k] (W*M 0)))
    (hsecond : (-δ) • u= -(u ∣[k] A0)-(δ*η) • (h ∣[k] Z0)) :
    δ • u-u ∣[k] A0-δ • (u ∣[k] B0)+u ∣[k] C0=0 := by
  have hh:=h_from_first u h δ η hδ hη hfirst
  have hZd : (GeneralLinearGroup.det Z0:ℝ)=1 := by
    change (GeneralLinearGroup.det (R*translation (4/5)*translation (-1)*E⁻¹*M 0):ℝ)=1
    simp only [map_mul,Units.val_mul,translation_det,det_one_inv _ E_det,M_det,mul_one]
    change (GeneralLinearGroup.det (translation (-1)*W*E):ℝ)=1
    rw [map_mul,map_mul,Units.val_mul,Units.val_mul,translation_det,W_det,E_det]
    norm_num
  rw [hh,sub_slash,det_one_smul _ hZd,det_one_smul _ hZd,
    ← SlashAction.slash_mul,← SlashAction.slash_mul,branch_B0,branch_C0] at hsecond
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;>
    simp only [one_smul,neg_one_smul,one_mul,mul_one,neg_mul,neg_neg,neg_sub] at hsecond ⊢ <;>
      linear_combination -hsecond

/-- Once the two branch relations are known, both auxiliary defects vanish. -/
theorem two_defects_zero {k : ℕ} (hk : 0<k) (u h : ℍ→ℂ) (hu : MDiff u)
    (δ η : ℂ) (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hK : u ∣[(k:ℤ)] K=η • u) (hL : u ∣[(k:ℤ)] L=(-δ*η) • u)
    (hfirst : δ • (u ∣[(k:ℤ)] translation (-2/3))=
      u ∣[(k:ℤ)] (translation (-1)*M 1)+(δ*η) • (h ∣[(k:ℤ)] (W*M 0)))
    (hsecond : (-δ) • u= -(u ∣[(k:ℤ)] A0)-(δ*η) • (h ∣[(k:ℤ)] Z0)) : u=0 ∧ h=0 := by
  have hz:=defect_zero_of_four_term hk u hu δ η hδ hη hK hL
    (four_term_of_two_relations u h δ η hδ hη hfirst hsecond)
  refine ⟨hz,?_⟩
  rw [h_from_first u h δ η hδ hη hfirst,hz]
  simp

#print axioms h_from_first
#print axioms four_term_of_two_relations
#print axioms two_defects_zero
end QuantitativeArithmeticSmallLevelTwentyTwo
