module

public import QuantitativeArithmeticSmallLevelTwentyTwoFinishMatricesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

private theorem sub_slash (F G : ℍ→ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (F-G) ∣[k] M=F ∣[k] M-G ∣[k] M := by
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]

/-- The four-term relation forces the first dilation eigenlaw. The input
relation itself is explicit and is not asserted here for original solutions. -/
theorem dilation_of_four_term {k : ℕ} (hk : 0<k) (u : ℍ→ℂ) (hu : MDiff u)
    (δ η : ℂ) (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hK : u ∣[(k:ℤ)] K=η • u)
    (hfour : δ • u-u ∣[(k:ℤ)] A0-δ • (u ∣[(k:ℤ)] B0)+u ∣[(k:ℤ)] C0=0) :
    u ∣[(k:ℤ)] A0=δ • u := by
  let w:=δ • u-u ∣[(k:ℤ)] A0
  have hw : MDiff w := by
    rcases hδ with h|h
    · simpa only [w,h,one_smul] using hu.sub (hu.slash (k:ℤ) A0)
    · simpa only [w,h,neg_one_smul] using hu.neg.sub (hu.slash (k:ℤ) A0)
  have hsign : -δ*η=1 ∨ -δ*η= -1 := by
    rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> norm_num
  have hwZ : w ∣[(k:ℤ)] Z=(-δ*η) • w := by
    dsimp only [w]
    rw [sub_slash,det_one_smul _ Z_det,
      ← SlashAction.slash_mul,A0_Z,SlashAction.slash_mul,hK,det_one_smul _ B0_det,
      ← K_C0,SlashAction.slash_mul,hK,det_one_smul _ C0_det]
    rcases hδ with hδ|hδ <;> rcases hη with hη|hη <;>
      simp only [hδ,hη,one_smul,neg_one_smul,neg_mul,one_mul,mul_one,neg_neg,
        neg_sub] at hfour ⊢ <;> first | linear_combination hfour | linear_combination -hfour
  have hz:=Z_eigen_zero hk w hw (-δ*η) hsign hwZ
  exact (sub_eq_zero.mp hz).symm

/-- The two explicit elliptic matrices close the auxiliary defect once
its four-term relation and the two already-known symmetries are available. -/
theorem defect_zero_of_four_term {k : ℕ} (hk : 0<k) (u : ℍ→ℂ) (hu : MDiff u)
    (δ η : ℂ) (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hK : u ∣[(k:ℤ)] K=η • u)
    (hL : u ∣[(k:ℤ)] L=(-δ*η) • u)
    (hfour : δ • u-u ∣[(k:ℤ)] A0-δ • (u ∣[(k:ℤ)] B0)+u ∣[(k:ℤ)] C0=0) : u=0 := by
  have hA:=dilation_of_four_term hk u hu δ η hδ hη hK hfour
  have hLd : (GeneralLinearGroup.det L:ℝ)=1 := by
    rw [L_explicit]
    exact matrix_det _ _ _ _ _
  have hV : u ∣[(k:ℤ)] V=(-1:ℂ) • u := by
    rw [← K_L_A0,SlashAction.slash_mul,SlashAction.slash_mul,hK,det_one_smul _ hLd,
      hL,det_one_smul _ A0_det,det_one_smul _ A0_det,hA,smul_smul,smul_smul]
    rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> simp
  exact V_eigen_zero hk u hu (-1) (Or.inr rfl) hV

#print axioms dilation_of_four_term
#print axioms defect_zero_of_four_term
end QuantitativeArithmeticSmallLevelTwentyTwo
