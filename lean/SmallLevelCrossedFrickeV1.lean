module
public import SmallLevelNormalizedFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelNormalized
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- Individual additive laws may exchange two centers. The resulting matrix
invariance uses the original common multiplier without dividing by it. -/
theorem crossed_of_fricke (N L k : ℕ) (hN : 0<N) (hL : 0<L) (r t : ℝ)
    (F : ℂ→ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ,0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (hG : ∀ z : ℂ,0<z.im → F (z+r)=
      χ/(((Real.sqrt L:ℂ)*z)^k)*F (-1/((L:ℂ)*z)+t)) :
    (fun z : ℍ => F z) ∣[(k:ℤ)]
      ((fricke N hN)⁻¹*translation t*fricke L hL*(translation r)⁻¹)=
        (fun z : ℍ => F z) := by
  let f : ℍ→ℂ := fun z => F z
  have htw : f ∣[(k:ℤ)] translation r=
      χ • ((f ∣[(k:ℤ)] translation t) ∣[(k:ℤ)] fricke L hL) := by
    funext z
    rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (fricke_det _ _),fricke_denom,
      translation_slash,translation_slash]
    simp only [f,translation_point,fricke_point]
    simpa only [zpow_neg,zpow_natCast,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
      using hG z z.im_pos
  have hf:=fricke_inverse_law N k hN F χ hF
  have hbranch : f ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation t*fricke L hL)=
      f ∣[(k:ℤ)] translation r := by
    simp only [SlashAction.slash_mul,f,hf,
      det_one_smul _ (translation_det _),det_one_smul _ (fricke_det _ _)]
    exact htw.symm
  have h:=congrArg (fun g : ℍ→ℂ => g ∣[(k:ℤ)] (translation r)⁻¹) hbranch
  simpa only [←SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

#print axioms crossed_of_fricke
end SmallLevelNormalized
