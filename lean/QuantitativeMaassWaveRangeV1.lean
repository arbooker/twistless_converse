module

public import QuantitativeMaassWaveCFCV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def dampedOperator (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  cfc (p := IsSelfAdjoint) (dampedCosine t) A

/-- Extension of the damped cosine from the actual dense resolvent range. -/
def rangeCosine (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (cfc (p := IsSelfAdjoint) (dampedCosine t) A).toLinearMap.extendOfNorm A.toLinearMap

theorem rangeCosine_range (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hd : DenseRange A)
    (t : ℝ) (v : H) : rangeCosine A t (A v)=cfc (dampedCosine t) A v := by
  exact LinearMap.extendOfNorm_eq (f := (cfc (p := IsSelfAdjoint) (dampedCosine t) A).toLinearMap)
    (e := A.toLinearMap) hd ⟨1,fun x => by
      change ‖cfc (p := IsSelfAdjoint) (dampedCosine t) A x‖≤1*‖A x‖
      rw [one_mul]
      exact dampedCosine_apply_norm_le A hA t x⟩ v

theorem rangeCosine_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hd : DenseRange A)
    (t : ℝ) : ‖rangeCosine A t‖≤1 := by
  exact LinearMap.opNorm_extendOfNorm_le
    (f := (cfc (p := IsSelfAdjoint) (dampedCosine t) A).toLinearMap)
    (e := A.toLinearMap) hd zero_le_one
    (fun x => by
      change ‖cfc (p := IsSelfAdjoint) (dampedCosine t) A x‖≤1*‖A x‖
      rw [one_mul]
      exact dampedCosine_apply_norm_le A hA t x)

theorem rangeCosine_apply_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hd : DenseRange A)
    (t : ℝ) (v : H) : ‖rangeCosine A t v‖≤‖v‖ :=
  ((rangeCosine A t).le_opNorm v).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (rangeCosine_norm_le A hA hd t) (norm_nonneg v))

theorem dampedCosine_zero : dampedCosine 0=id := by ext s; simp [dampedCosine]

theorem rangeCosine_zero (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hd : DenseRange A) :
    rangeCosine A 0=ContinuousLinearMap.id ℂ _ := by
  apply DFunLike.coe_injective
  apply hd.equalizer (rangeCosine A 0).continuous (ContinuousLinearMap.id ℂ _).continuous
  funext v
  change rangeCosine A 0 (A v)=A v
  rw [rangeCosine_range A hA hd,dampedCosine_zero,cfc_id ℝ A hA]

theorem dampedCosine_neg (t : ℝ) : dampedCosine (-t)=dampedCosine t := by
  ext s
  simp [dampedCosine]

theorem rangeCosine_neg (A : H →L[ℂ] H) (t : ℝ) : rangeCosine A (-t)=rangeCosine A t := by
  unfold rangeCosine
  rw [dampedCosine_neg]

theorem rangeCosine_commute (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hd : DenseRange A)
    (t : ℝ) : Commute (rangeCosine A t) A := by
  apply DFunLike.coe_injective
  apply hd.equalizer ((rangeCosine A t)*A).continuous (A*(rangeCosine A t)).continuous
  funext v
  change rangeCosine A t (A (A v))=A (rangeCosine A t (A v))
  rw [rangeCosine_range A hA hd,rangeCosine_range A hA hd]
  have h := cfc_commute_cfc (p := IsSelfAdjoint) (dampedCosine t) (id : ℝ → ℝ) A
  rw [cfc_id ℝ A hA] at h
  exact congrArg (fun B : H →L[ℂ] H => B v) h.eq

#print axioms rangeCosine_range
#print axioms rangeCosine_norm_le
#print axioms rangeCosine_commute

end QuantitativeMaass.Wave
