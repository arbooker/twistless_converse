module

public import SmallLevelTransversalV1
public import SmallLevelOriginalV1
public import FinitenessOriginalFrickeV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelGenerators

open Matrix UpperHalfPlane ModularGroup
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

theorem lower_point (N : ℕ) (z : ℍ) :
    ((lower N • z : ℍ) : ℂ)=(z:ℂ)/((N:ℂ)*(z:ℂ)+1) := by
  rw [coe_specialLinearGroup_apply]
  simp [lower]

theorem lower_denom (N : ℕ) (z : ℍ) :
    denom (lower N) z=(N:ℂ)*(z:ℂ)+1 := by
  simp [ModularGroup.denom_apply, lower]

/-- Periodicity and the single original Fricke law force the lower
unipotent transformation. No twisted functional equation is assumed. -/
theorem lower_of_fricke {N k : ℕ} (hN : 0<N) (F : ℂ → ℂ) (χ : ℂ)
    (hp : ∀ z, F (z+1)=F z)
    (hfr : ∀ z : ℂ, 0<z.im →
      F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z))) :
    (fun z : ℍ => F z) ∣[(k:ℤ)] lower N = (fun z : ℍ => F z) := by
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
  have hp' : F ((-1/((N:ℂ)*(z:ℂ)))-1)=F (-1/((N:ℂ)*(z:ℂ))) := by
    simpa only [sub_add_cancel] using (hp ((-1/((N:ℂ)*(z:ℂ)))-1)).symm
  have hez := hfr z z.im_pos
  have hew := hfr w w.im_pos
  rw [hident, hp'] at hew
  have ez : F z*((Real.sqrt N:ℂ)*(z:ℂ))^k=
      χ*F (-1/((N:ℂ)*(z:ℂ))) := by
    rw [hez]
    field_simp
  have ew : F w*((Real.sqrt N:ℂ)*(w:ℂ))^k=
      χ*F (-1/((N:ℂ)*(z:ℂ))) := by
    rw [hew]
    field_simp [w.ne_zero]
  have halg : ((N:ℂ)*(z:ℂ)+1)*((Real.sqrt N:ℂ)*(w:ℂ))=
      (Real.sqrt N:ℂ)*(z:ℂ) := by
    rw [hw]
    calc
      _ = ((Real.sqrt N:ℂ)*(z:ℂ))*(((N:ℂ)*(z:ℂ)+1)/((N:ℂ)*(z:ℂ)+1)) := by ring
      _ = _ := by rw [div_self hd, mul_one]
  have he : F w=F z*((N:ℂ)*(z:ℂ)+1)^k := by
    apply (mul_right_cancel₀ (pow_ne_zero k (mul_ne_zero hs w.ne_zero)))
    rw [ew, ← ez, mul_assoc, ← mul_pow, halg]
  rw [ModularForm.SL_slash_apply, lower_denom]
  change F w*((N:ℂ)*(z:ℂ)+1)^(-(k:ℤ))=F z
  rw [he, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hd), mul_one]

theorem original_T (k : ℕ) (f : ℕ → ℂ) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] T=
      SmallLevelOriginal.fourierFunction k f := by
  funext z
  rw [ModularForm.SL_slash_apply, modular_T_smul]
  have hd : denom T z=1 := by simp [ModularGroup.denom_apply, ModularGroup.T]
  rw [hd, one_zpow, mul_one]
  simpa only [SmallLevelOriginal.fourierFunction, coe_vadd, Complex.ofReal_one,
    add_comm] using periodic (fullCoefficients f k) (z:ℂ)

theorem original_lower {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : IsSolution N k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] lower N=
      SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨χ, _, hχ⟩ := FinitenessOriginalFricke.solution_fricke hN hf
  exact lower_of_fricke hN _ χ (periodic _) hχ

def slashStabilizer (k : ℤ) (F : ℍ → ℂ) : Subgroup SL(2,ℤ) where
  carrier := {γ | F ∣[k] γ=F}
  one_mem' := by simp
  mul_mem' := by
    intro γ δ hγ hδ
    change F ∣[k] (γ*δ)=F
    rw [SlashAction.slash_mul, hγ, hδ]
  inv_mem' := by
    intro γ hγ
    change F ∣[k] γ⁻¹=F
    have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] γ⁻¹) hγ
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using hh.symm

#print axioms lower_of_fricke
#print axioms original_T
#print axioms original_lower

end SmallLevelGenerators
