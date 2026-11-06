module

public import QuantitativeSpectralExceptionalGeometryTriangularV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open Matrix UpperHalfPlane Set AsymptoticRegularBranchFamily
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalDiscriminant QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalReducedRows QuantitativeSpectralFiniteReduction
open scoped MatrixGroups Pointwise

/-- A rational branch on a fixed horizontal interval needs only finitely
many actual Gamma0 reducers near infinity. Its cusp-height loss is the
positive affine slope, and all reducers are independent of H. -/
theorem finite_cusp_branch_reduction (N : ℕ) (b : Branch) (R : ℝ) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∃ F : Finset SL(2,ℤ),
      (∀ g ∈ F, g ∈ CongruenceSubgroup.Gamma0 N) ∧
      ∀ H : ℝ, ∀ z : ℍ, |z.re| ≤ R → Y ≤ z.im → z.im ≤ H/C →
        ∃ g ∈ F, (integralLabel g * label b) • z ∈ wideCompactCover N H := by
  classical
  obtain ⟨U,α,β,hα,hchart⟩ := branch_affine_chart b
  let q (n : ℤ) : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.mk (ModularGroup.T^(-n)*U⁻¹)
  let g (n : ℤ) : SL(2,ℤ) := (q n).out⁻¹*(ModularGroup.T^(-n)*U⁻¹)
  let I : Finset ℤ := Finset.Icc ⌊α*(-R)+β⌋ ⌊α*R+β⌋
  have hg (n : ℤ) : g n ∈ CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (q n))
  refine ⟨α,α⁻¹,hα,inv_pos.mpr hα,I.image g,?_,?_⟩
  · intro a ha
    obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp ha
    exact hg n
  · intro H z hx hy hhi
    let v := affine α hα β z
    let n : ℤ := ⌊v.re⌋
    have hvre : v.re = α*z.re+β := by simp [v,affine,Complex.mul_re]
    have hn : n ∈ I := by
      apply Finset.mem_Icc.mpr
      constructor
      · apply Int.floor_mono
        rw [hvre]
        linarith [mul_le_mul_of_nonneg_left (abs_le.mp hx).1 hα.le]
      · apply Int.floor_mono
        rw [hvre]
        linarith [mul_le_mul_of_nonneg_left (abs_le.mp hx).2 hα.le]
    have hlo : (1:ℝ) ≤ α*z.im := by
      have hh := mul_le_mul_of_nonneg_left hy hα.le
      simpa only [mul_inv_cancel₀ hα.ne'] using hh
    have htop : α*z.im ≤ H := by
      have hh := (le_div_iff₀ hα).mp hhi
      nlinarith
    refine ⟨g n,Finset.mem_image.mpr ⟨n,hn,rfl⟩,?_⟩
    apply mem_iUnion.mpr
    refine ⟨q n,ModularGroup.T^(-n) • v,?_,?_⟩
    · have hr0 := Int.floor_le v.re
      have hr1 := Int.lt_floor_add_one v.re
      change -1 ≤ (ModularGroup.T^(-n) • v).re ∧
        (ModularGroup.T^(-n) • v).re ≤ 2 ∧ 1/4 ≤ (ModularGroup.T^(-n) • v).im ∧
        (ModularGroup.T^(-n) • v).im ≤ H
      simp only [ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul,
        Int.cast_neg]
      change -1 ≤ v.re-(n:ℝ) ∧ v.re-(n:ℝ) ≤ 2 ∧ 1/4 ≤ v.im ∧ v.im ≤ H
      have him : v.im = α*z.im := affine_im α hα β z
      exact ⟨by change -1 ≤ v.re-(⌊v.re⌋:ℝ); linarith,
        by change v.re-(⌊v.re⌋:ℝ) ≤ 2; linarith,
        by rw [him]; linarith,by rwa [him]⟩
    · simp only [← map_inv,integralLabel_action,g,mul_smul,hchart,
        inv_smul_smul]
      rfl

/-- The finite cusp reducers are actual fixed words in any chosen Gamma0
generating set; no word length depends on the truncation height. -/
theorem finite_cusp_branch_words (N : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : Branch) (R : ℝ) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, ∀ z : ℍ, |z.re| ≤ R → Y ≤ z.im → z.im ≤ H/C →
        ∃ l ∈ W, (integralLabel l.prod * label b) • z ∈ wideCompactCover N H := by
  classical
  obtain ⟨C,Y,hC,hY,F,hF,hr⟩ := finite_cusp_branch_reduction N b R
  choose w hw using fun a : ↥F => congruence_word N S hS a.val (hF a.val a.property)
  refine ⟨C,Y,hC,hY,Finset.univ.image w,?_,?_⟩
  · intro l hl
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
    exact (hw a).2
  · intro H z hx hy ht
    obtain ⟨a,ha,haz⟩ := hr H z hx hy ht
    refine ⟨w ⟨a,ha⟩,Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,rfl⟩,?_⟩
    simpa only [(hw ⟨a,ha⟩).1] using haz

#print axioms finite_cusp_branch_reduction
#print axioms finite_cusp_branch_words

end QuantitativeSpectralExceptionalGeometry
