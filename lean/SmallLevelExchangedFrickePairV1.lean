module

public import SmallLevelNormalizedFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelNormalized
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- A Fricke law exchanging two even pairs yields the corresponding
normalized two-branch identity, with the original multiplier canceled. -/
theorem exchanged_pair_of_fricke (N L k : ℕ) (hN : 0<N) (hL : 0<L) (r t : ℝ)
    (F : ℂ→ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (hG : ∀ z : ℂ, 0<z.im → F (z+t)+F (z-t)=
      χ/(((Real.sqrt L:ℂ)*z)^k)*(F (-1/((L:ℂ)*z)+r)+F (-1/((L:ℂ)*z)-r))) :
    ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r*fricke L hL))+
      ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation (-r)*fricke L hL))=
      ((fun z : ℍ => F z) ∣[(k:ℤ)] translation t)+
      ((fun z : ℍ => F z) ∣[(k:ℤ)] translation (-t)) := by
  let f : ℍ→ℂ:=fun z => F z
  have hf:=fricke_inverse_law N k hN F χ hF
  have hp : (fun z : ℍ => F ((z:ℂ)+t)+F ((z:ℂ)-t))=
      χ • (((f ∣[(k:ℤ)] translation r)+(f ∣[(k:ℤ)] translation (-r))) ∣[(k:ℤ)] fricke L hL) := by
    funext z
    simp only [Pi.smul_apply,smul_eq_mul,SlashAction.add_slash,Pi.add_apply]
    rw [det_one_slash _ (fricke_det _ _),det_one_slash _ (fricke_det _ _),
      fricke_denom]
    simp only [translation_slash,f,translation_point,Complex.ofReal_neg,fricke_point]
    have h:=hG z z.im_pos
    simpa only [zpow_neg,zpow_natCast,div_eq_mul_inv,sub_eq_add_neg,
      mul_add,add_mul,mul_assoc,mul_comm,mul_left_comm] using h
  have ht : (fun z : ℍ => F ((z:ℂ)+t)+F ((z:ℂ)-t))=
      (f ∣[(k:ℤ)] translation t)+(f ∣[(k:ℤ)] translation (-t)) := by
    funext z
    simp only [Pi.add_apply,translation_slash,f,translation_point,Complex.ofReal_neg,sub_eq_add_neg]
  rw [ht] at hp
  calc
    _ = χ • (((f ∣[(k:ℤ)] translation r)+(f ∣[(k:ℤ)] translation (-r))) ∣[(k:ℤ)] fricke L hL) := by
      simp only [SlashAction.slash_mul,hf,det_one_smul _ (translation_det _),
        det_one_smul _ (fricke_det _ _)]
      rw [← smul_add,← SlashAction.add_slash]
    _ = _ := hp.symm

#print axioms exchanged_pair_of_fricke
end SmallLevelNormalized
