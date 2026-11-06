module

public import AsymptoticClassicalOldIntersectionGroupsV1
public import AsymptoticClassicalHeckeFormulaV1
public import AsymptoticClassicalTranslateEquivV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- The honest Fricke-old restriction image is exactly the image of the
 classical map f(z) ↦ f(p*z), including its nonzero scalar normalization. -/
theorem frickeOld_range_eq_degeneracy (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (k : ℤ) :
    LinearMap.range (restrict k (level_le_frickeOldLevel (Nat.mul_pos hp hM) (dvd_mul_left M p))) =
      LinearMap.range (degeneracy M p hp k) := by
  have he := frickeOldLevel_eq_dilationLevel M p hM hp
  have hpR : 0 < (dilationReal p hp).det.val := by rw [dilationReal_det]; exact_mod_cast hp
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    let gD : CuspForm (dilationLevel M p hp) k := CuspForm.mcast rfl g he.symm
    obtain ⟨a, ha⟩ := translateLinear_surjective (level M) k (dilationReal p hp) hpR gD
    refine ⟨(p : ℂ) ^ (k - 1) • a, ?_⟩
    apply DFunLike.coe_injective
    change (degeneracy M p hp k ((p : ℂ) ^ (k - 1) • a) : ℍ → ℂ) = (g : ℍ → ℂ)
    rw [map_smul, FunLike.coe_smul, scaled_degeneracy_coe]
    exact congrArg (fun h : CuspForm (dilationLevel M p hp) k => (h : ℍ → ℂ)) ha
  · rintro ⟨g, rfl⟩
    refine ⟨CuspForm.mcast rfl ((p : ℂ) ^ (1 - k) • CuspForm.translate g (dilationReal p hp)) he, ?_⟩
    apply CuspForm.ext
    intro z
    rfl

#print axioms frickeOld_range_eq_degeneracy

end AsymptoticClassicalCusp
