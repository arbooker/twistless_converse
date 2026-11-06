module

public import QuantitativeSpectralExceptionalGeometryV1
public import QuantitativeSpectralObservabilityFundamentalV1
public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open Matrix UpperHalfPlane Set AsymptoticCongruenceLabels
open QuantitativeSpectralObservability
open scoped MatrixGroups Modular Pointwise

/-- Proper discontinuity supplies finitely many literal modular matrices
reducing a fixed compact set into the closed standard fundamental domain. -/
theorem finite_compact_fd_reduction {s : Set ℍ} (hs : IsCompact s) :
    ∃ F : Finset SL(2,ℤ), ∀ z ∈ s, ∃ g ∈ F, g • z ∈ 𝒟 := by
  classical
  obtain ⟨B,hB,hband⟩ := compact_height_band hs
  have hf : {g : GL (Fin 2) ℝ | g ∈ 𝒮ℒ ∧
      (g • s ∩ ModularGroup.truncatedFundamentalDomain B).Nonempty}.Finite :=
    (Subgroup.properlyDiscontinuousSMul_iff 𝒮ℒ).mp inferInstance hs
      (ModularGroup.isCompact_truncatedFundamentalDomain B)
  have hinj : Function.Injective (SpecialLinearGroup.mapGL ℝ : SL(2,ℤ) → GL (Fin 2) ℝ) :=
    SpecialLinearGroup.mapGL_injective
  have hpre := Set.Finite.preimage hinj.injOn hf
  refine ⟨hpre.toFinset,?_⟩
  intro z hz
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨g,?_,hg⟩
  apply hpre.mem_toFinset.mpr
  refine ⟨⟨g,rfl⟩,g • z,⟨z,hz,rfl⟩,hg,?_⟩
  exact integral_height_upper g (inv_pos.mpr hB) (by simp) z (hband z hz).1 (hband z hz).2

/-- A fixed finite modular reduction family works on the whole wide
strip. The compact lower part and high translations are treated separately. -/
theorem finite_wide_strip_fd_reduction :
    ∃ F : Finset SL(2,ℤ), ∀ z : ℍ,
      -1 ≤ z.re → z.re ≤ 2 → (1:ℝ)/4 ≤ z.im →
        ∃ g ∈ F, g • z ∈ 𝒟 := by
  classical
  obtain ⟨F,hF⟩ := finite_compact_fd_reduction (wideBox_compact 1)
  let I : Finset ℤ := Finset.Icc (-1) 2
  refine ⟨F ∪ I.image (fun n => ModularGroup.T^(-n)),?_⟩
  intro z hx₀ hx₁ hy
  by_cases hz : z.im ≤ 1
  · obtain ⟨g,hg,hgz⟩ := hF z ⟨hx₀,hx₁,hy,hz⟩
    exact ⟨g,Finset.mem_union_left _ hg,hgz⟩
  · let n : ℤ := ⌊z.re+1/2⌋
    have hn : n ∈ I := by
      apply Finset.mem_Icc.mpr
      constructor
      · exact Int.le_floor.mpr (by norm_num; linarith)
      · have hh : n < 3 := Int.floor_lt.mpr (by norm_num; linarith)
        omega
    refine ⟨ModularGroup.T^(-n),Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨n,hn,rfl⟩),?_⟩
    have hr₀ := Int.floor_le (z.re+1/2)
    have hr₁ := Int.lt_floor_add_one (z.re+1/2)
    have hre : (ModularGroup.T^(-n) • z).re = z.re-(n:ℝ) := by
      simp only [ModularGroup.re_T_zpow_smul,Int.cast_neg,sub_eq_add_neg]
    have him : (ModularGroup.T^(-n) • z).im = z.im := ModularGroup.im_T_zpow_smul _ _
    constructor
    · rw [Complex.normSq_apply]
      change 1 ≤ (ModularGroup.T^(-n) • z).re*(ModularGroup.T^(-n) • z).re +
        (ModularGroup.T^(-n) • z).im*(ModularGroup.T^(-n) • z).im
      rw [him]
      nlinarith [sq_nonneg (ModularGroup.T^(-n) • z).re,z.im_pos]
    · rw [hre,abs_le]
      change -((1:ℝ)/2) ≤ z.re-(⌊z.re+1/2⌋:ℝ) ∧ z.re-(⌊z.re+1/2⌋:ℝ) ≤ 1/2
      constructor <;> linarith

/-- The same fixed reducers land in the genuinely sampled fundamental
truncation without enlarging H, once H is at least four. -/
theorem finite_wide_box_fd_reduction :
    ∃ F : Finset SL(2,ℤ), ∀ H : ℝ, 4 ≤ H → ∀ z ∈ wideBox H,
      ∃ g ∈ F, g • z ∈ 𝒟 ∧ (g • z).im ≤ H := by
  obtain ⟨F,hF⟩ := finite_wide_strip_fd_reduction
  refine ⟨F,?_⟩
  intro H hH z hz
  obtain ⟨g,hg,hgz⟩ := hF z hz.1 hz.2.1 hz.2.2.1
  exact ⟨g,hg,hgz,integral_height_upper g (by norm_num : (0:ℝ)<1/4)
    (by norm_num; exact hH) z hz.2.2.1 hz.2.2.2⟩

#print axioms finite_compact_fd_reduction
#print axioms finite_wide_box_fd_reduction

end QuantitativeSpectralExceptionalGeometry
