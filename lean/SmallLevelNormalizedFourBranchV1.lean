module
public import SmallLevelNormalizedFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelNormalized
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- Four coherent Fricke branches, without division by the common
functional-equation scalar. -/
theorem four_branch_of_fricke (N L k : ℕ) (hN : 0<N) (hL : 0<L)
    (r₁ r₂ r₃ r₄ : ℝ) (F : ℂ→ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ,0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (hG : ∀ z : ℂ,0<z.im → F (z+r₁)+F (z+r₂)+F (z+r₃)+F (z+r₄)=
      χ/(((Real.sqrt L:ℂ)*z)^k)*(F (-1/((L:ℂ)*z)+r₁)+F (-1/((L:ℂ)*z)+r₂)+
        F (-1/((L:ℂ)*z)+r₃)+F (-1/((L:ℂ)*z)+r₄))) :
    ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r₁*fricke L hL))+
    ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r₂*fricke L hL))+
    ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r₃*fricke L hL))+
    ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r₄*fricke L hL))=
    ((fun z : ℍ => F z) ∣[(k:ℤ)] translation r₁)+
    ((fun z : ℍ => F z) ∣[(k:ℤ)] translation r₂)+
    ((fun z : ℍ => F z) ∣[(k:ℤ)] translation r₃)+
    ((fun z : ℍ => F z) ∣[(k:ℤ)] translation r₄) := by
  let f : ℍ→ℂ := fun z => F z
  let G : ℂ→ℂ := fun z => F (z+r₁)+F (z+r₂)+F (z+r₃)+F (z+r₄)
  have htw := fricke_law L k hL G χ hG
  have hf := fricke_inverse_law N k hN F χ hF
  have ht : (fun z : ℍ => G z)=
      (f ∣[(k:ℤ)] translation r₁)+(f ∣[(k:ℤ)] translation r₂)+
      (f ∣[(k:ℤ)] translation r₃)+(f ∣[(k:ℤ)] translation r₄) := by
    funext z
    simp only [Pi.add_apply,translation_slash,f,G,translation_point]
  rw [ht,SlashAction.add_slash,SlashAction.add_slash,SlashAction.add_slash,
    smul_add,smul_add,smul_add] at htw
  simpa only [SlashAction.slash_mul,hf,det_one_smul _ (translation_det _),
    det_one_smul _ (fricke_det _ _),f] using htw.symm

#print axioms four_branch_of_fricke
end SmallLevelNormalized
