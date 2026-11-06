module

public import SmallLevelGoodHeckeFiveV1
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelFiniteHeckeStep
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- An exact permutation of Hecke branches forces the only unknown
invariance. The translating matrix is arbitrary at eigenvalue zero. -/
theorem one_missing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℍ → ℂ) (k : ℤ) (M : ι → GL (Fin 2) ℝ)
    (B : SL(2,ℤ)) (γ : ι → SL(2,ℤ)) (π : Equiv.Perm ι) (bad : ι) (lam : ℂ)
    (he : (∑ i, F ∣[k] M i)=lam • F)
    (hB : lam=0 ∨ F ∣[k] B=F)
    (hb : ∀ i, M i*SpecialLinearGroup.mapGL ℝ B=SpecialLinearGroup.mapGL ℝ (γ i)*M (π i))
    (hk : ∀ i, i≠bad → F ∣[k] γ i=F) : F ∣[k] γ bad=F := by
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] B) he
  simp only [SlashAction.sum_slash,ModularForm.SL_smul_slash] at hh
  have hbranch (i : ι) : (F ∣[k] M i) ∣[k] B=(F ∣[k] γ i) ∣[k] M (π i) := by
    change (F ∣[k] M i) ∣[k] SpecialLinearGroup.mapGL ℝ B=
      (F ∣[k] SpecialLinearGroup.mapGL ℝ (γ i)) ∣[k] M (π i)
    rw [← SlashAction.slash_mul,hb,SlashAction.slash_mul]
  simp only [hbranch] at hh
  have hscalar : lam • (F ∣[k] B)=lam • F := by
    rcases hB with hB|hB
    · simp only [hB,zero_smul]
    · rw [hB]
  have hperm : (∑ i, F ∣[k] M (π i))=∑ i, F ∣[k] M i := Equiv.sum_comp π (fun i : ι => F ∣[k] M i)
  have hs : (∑ i, ((F ∣[k] γ i)-F) ∣[k] M (π i))=0 := by
    simp only [SmallLevelEleven.sub_slash,Finset.sum_sub_distrib]
    rw [hh,hscalar,hperm,he,sub_self]
  have ht : (∑ i, ((F ∣[k] γ i)-F) ∣[k] M (π i))=
      ((F ∣[k] γ bad)-F) ∣[k] M (π bad) := by
    apply Finset.sum_eq_single bad
    · intro i _ hi
      rw [hk i hi,sub_self,SlashAction.zero_slash]
    · simp
  rw [ht] at hs
  have hc := congrArg (fun G : ℍ → ℂ => G ∣[k] (M (π bad))⁻¹) hs
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,SlashAction.zero_slash] at hc
  exact sub_eq_zero.mp hc

#print axioms one_missing
end SmallLevelFiniteHeckeStep
