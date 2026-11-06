module

public import SmallLevelFrickeGeneratorsV1
public import FinitenessComplexGeometryV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelGenerators
open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm

/-- A translation eigenvalue is preserved by Fricke conjugation. The
proof clears denominators and never divides by the Fricke scalar. -/
theorem lower_eigen_of_fricke {N k : ℕ} (hN : 0<N) (F : ℂ → ℂ) (χ α : ℂ)
    (hp : ∀ z : ℂ, 0<z.im → F (z-1)=α*F z)
    (hfr : ∀ z : ℂ, 0<z.im →
      F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z))) :
    (fun z : ℍ => F z) ∣[(k:ℤ)] lower N = α • (fun z : ℍ => F z) := by
  funext z
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hz : (z:ℂ)≠0 := z.ne_zero
  have hd : (N:ℂ)*(z:ℂ)+1≠0 := by
    rw [← lower_denom]
    exact denom_ne_zero _ _
  let w : ℍ := lower N • z
  have hw : (w:ℂ)=(z:ℂ)/((N:ℂ)*(z:ℂ)+1) := lower_point N z
  have hident : -1/((N:ℂ)*(w:ℂ))=(-1/((N:ℂ)*(z:ℂ)))-1 := by
    rw [hw]
    field_simp
    ring
  have hr : 0<(-1/((N:ℂ)*(z:ℂ))).im := by
    simpa only [Complex.ofReal_natCast] using
      FinitenessComplexGeometry.reflected_im_pos
        (L:=(N:ℝ)) (by exact_mod_cast hN) z.im_pos
  have hp' := hp (-1/((N:ℂ)*(z:ℂ))) hr
  have hez := hfr z z.im_pos
  have hew := hfr w w.im_pos
  rw [hident, hp'] at hew
  have ez : F z*((Real.sqrt N:ℂ)*(z:ℂ))^k=
      χ*F (-1/((N:ℂ)*(z:ℂ))) := by
    rw [hez]
    field_simp
  have ew : F w*((Real.sqrt N:ℂ)*(w:ℂ))^k=
      α*(χ*F (-1/((N:ℂ)*(z:ℂ)))) := by
    rw [hew]
    field_simp [w.ne_zero]
  have halg : ((N:ℂ)*(z:ℂ)+1)*((Real.sqrt N:ℂ)*(w:ℂ))=
      (Real.sqrt N:ℂ)*(z:ℂ) := by
    rw [hw]
    calc
      _ = ((Real.sqrt N:ℂ)*(z:ℂ))*(((N:ℂ)*(z:ℂ)+1)/((N:ℂ)*(z:ℂ)+1)) := by ring
      _ = _ := by rw [div_self hd, mul_one]
  have he : F w=α*(F z*((N:ℂ)*(z:ℂ)+1)^k) := by
    apply (mul_right_cancel₀ (pow_ne_zero k (mul_ne_zero hs w.ne_zero)))
    rw [ew, ← ez, mul_assoc, mul_assoc, ← mul_pow, halg]
  rw [ModularForm.SL_slash_apply, lower_denom]
  change F w*((N:ℂ)*(z:ℂ)+1)^(-(k:ℤ))=α*F z
  rw [he, zpow_neg, zpow_natCast, mul_assoc, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hd), mul_one]

#print axioms lower_eigen_of_fricke

end SmallLevelGenerators
