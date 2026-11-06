module

public import SmallLevelOddFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelGenerators

open Matrix UpperHalfPlane ModularGroup
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

def halfConjugate (b : ℕ) : SL(2,ℤ) :=
  ⟨!![1+2*(b:ℤ),-(b:ℤ);4*(b:ℤ),1-2*(b:ℤ)], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring⟩

def shiftMinusHalf (z : ℍ) : ℍ := ⟨(z:ℂ)-1/2, by simpa using z.im_pos⟩

theorem halfConjugate_denom (b : ℕ) (z : ℍ) :
    denom (lower (4*b)) (shiftMinusHalf z)=denom (halfConjugate b) z := by
  rw [lower_denom]
  simp [ModularGroup.denom_apply, halfConjugate, shiftMinusHalf]
  ring

theorem halfConjugate_point (b : ℕ) (z : ℍ) :
    ((lower (4*b) • shiftMinusHalf z : ℍ):ℂ)+1/2=
      ((halfConjugate b • z : ℍ):ℂ) := by
  rw [lower_point]
  have hp : ((halfConjugate b • z : ℍ):ℂ)=
      ((1+2*(b:ℂ))*(z:ℂ)-(b:ℂ))/(4*(b:ℂ)*(z:ℂ)+(1-2*(b:ℂ))) := by
    rw [coe_specialLinearGroup_apply]
    simp [halfConjugate, sub_eq_add_neg]
  rw [hp]
  simp only [shiftMinusHalf, UpperHalfPlane.coe_mk, Nat.cast_mul, Nat.cast_ofNat]
  have hd : (4:ℂ)*b*(z:ℂ)+(1-2*(b:ℂ))≠0 := by
    have h := denom_ne_zero (halfConjugate b) z
    simpa [ModularGroup.denom_apply, halfConjugate] using h
  rw [show (4:ℂ)*b*((z:ℂ)-1/2)+1=4*b*(z:ℂ)+(1-2*b) by ring]
  field_simp [hd]
  ring_nf
  have hd' : 1+(z:ℂ)*(b:ℂ)*4-(b:ℂ)*2≠0 := by
    convert hd using 1
    ring
  field_simp [hd']
  ring

theorem halfConjugate_of_lower (b k : ℕ) (F : ℂ → ℂ)
    (h : (fun z : ℍ => F ((z:ℂ)+1/2)) ∣[(k:ℤ)] lower (4*b)=
      (fun z : ℍ => F ((z:ℂ)+1/2))) :
    (fun z : ℍ => F z) ∣[(k:ℤ)] halfConjugate b=(fun z : ℍ => F z) := by
  funext z
  have hh := congrFun h (shiftMinusHalf z)
  rw [ModularForm.SL_slash_apply, halfConjugate_denom] at hh
  rw [halfConjugate_point] at hh
  rw [ModularForm.SL_slash_apply]
  simpa only [shiftMinusHalf, UpperHalfPlane.coe_mk,
    sub_add_cancel] using hh

/-- A one-term Ramanujan twist supplies the half-translation conjugate
of the lower unipotent whenever the level is divisible by four. -/
theorem original_halfConjugate {b k : ℕ} (hb : 0<b) {f : ℕ → ℂ}
    (hf : IsSolution (4*b) k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] halfConjugate b=
      SmallLevelOriginal.fourierFunction k f := by
  have hN : 0<4*b := by omega
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  have hlcm : Nat.lcm (4*b) (2^2)=4*b := by
    apply Nat.dvd_antisymm
    · exact Nat.lcm_dvd (dvd_refl _) ⟨b, rfl⟩
    · exact Nat.dvd_lcm_left _ _
  apply halfConjugate_of_lower
  apply lower_of_fricke (k:=k) hN (fun z : ℂ => fourier (fullCoefficients f k) (z+1/2))
    (FinitenessNormalizedTwistProduct.root (4*b) f 2*ε*Complex.I^k)
  · intro z
    rw [show z+1+1/2=(z+1/2)+1 by ring]
    exact periodic _ _
  · intro z hz
    have h := hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) :
        FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    simpa only [hlcm, ht] using h

#print axioms halfConjugate_of_lower
#print axioms original_halfConjugate

end SmallLevelGenerators
