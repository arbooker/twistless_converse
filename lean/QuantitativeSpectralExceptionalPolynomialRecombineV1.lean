module

public import QuantitativeSpectralExceptionalPolynomialNormV1
public import QuantitativeSpectralExceptionalFundamentalAssemblyV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularBranchFamily
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

variable {ι : Type*} [Fintype ι]

theorem generatorRecombine_norm_of_inverse (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : ι → List SL(2,ℤ)) (hw : ∀ i a, a ∈ w i → a ∈ A) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε P : ℝ} (hε : 0 < ε) (t : ℕ) (hP : 0≤P)
    (hbase : ∀ z∈s, (AsymptoticCompactBranch.cap ε t z)⁻¹≤P)
    (hbranch : ∀ i z, z∈image (b i) s → (AsymptoticCompactBranch.cap ε t z)⁻¹≤P)
    (hword : ∀ i k z, z∈image (b i) s →
      (AsymptoticCompactBranch.cap ε t (AsymptoticCongruenceLabels.integralLabel ((w i).drop k).prod • z))⁻¹≤P)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    ‖generatorRecombine A b w hw c hs hε t Ds Db x‖ ≤
      P + ∑ i, ‖c i‖ * P * ((w i).length*P) := by
  apply opNorm_le_bound _ (by positivity)
  intro v
  simp only [generatorRecombine,_root_.add_apply,_root_.sum_apply,smul_apply,comp_apply,
    PiLp.proj_apply,add_mul,Finset.sum_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).le_of_opNorm_le
      (unweight_norm_of_bound hε t Ds hP hbase x) _).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v none) hP)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul]
    have hp := (pull (label (b i))).le_of_opNorm_le (pull_norm _)
      (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x
        (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i) v))
    simp only [one_mul] at hp
    have hu := (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x).le_of_opNorm_le
      (unweight_norm_of_bound hε t (Db i) hP (hbranch i) x)
      (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i) v)
    have hl := (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i)).le_of_opNorm_le
      (wordRecombine_norm_of_inverse A (w i) (hw i) (image_compact (b i) hs) hε t hP (hword i) x) v
    have hh := (hp.trans hu).trans (mul_le_mul_of_nonneg_left hl hP)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (c i))).trans_eq (by ring)


#print axioms generatorRecombine_norm_of_inverse

end QuantitativeSpectralExceptionalReducedRows
