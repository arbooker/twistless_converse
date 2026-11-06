module

public import SmallLevelThirtyNormalizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
@[expose] public noncomputable section

namespace SmallLevelThirty

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def charGen (δ β η : ℂ) : Fin 5 → ℂ := ![1,δ,β,η,δ]
def charRep (δ β η : ℂ) : Fin 8 → ℂ := ![1,δ,β,δ*β,η,δ*η,β*η,δ*β*η]

theorem character_step (δ β η : ℂ) (hδ : δ=1 ∨ δ= -1) (hβ : β=1 ∨ β= -1) (hη : η=1 ∨ η= -1) :
    ∀ r j, charRep δ β η r*charGen δ β η j=charRep δ β η (nextIndex r j) := by
  rcases hδ with rfl|rfl <;> rcases hβ with rfl|rfl <;> rcases hη with rfl|rfl <;>
    intro r j <;> fin_cases r <;> fin_cases j <;> norm_num [charRep,charGen,nextIndex,edgeData]

theorem original_generators (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 (2*m) f) :
    ∃ β η : ℂ, (β=1 ∨ β= -1) ∧ (η=1 ∨ η= -1) ∧ ∀ j,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realGen j=
        charGen (FinitenessNormalizedTwistProduct.root 30 f 2) β η j •
          SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨β,hβ,hB⟩ := SmallLevelThirtyB.original_A m hm hf
  obtain ⟨η,hη,hW⟩ := original_fricke_sign (by decide : 0<30) m hf
  refine ⟨β,η,hβ,hη,?_⟩
  intro j
  fin_cases j
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realGen 0=
      charGen (FinitenessNormalizedTwistProduct.root 30 f 2) β η 0 • SmallLevelOriginal.fourierFunction (2*m) f
    rw [realGen_0]
    simp only [charGen,Matrix.cons_val_zero,one_smul]
    change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] ModularGroup.T=
      SmallLevelOriginal.fourierFunction (2*m) f
    exact SmallLevelGenerators.original_T (2*m) f
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realGen 1=
      charGen (FinitenessNormalizedTwistProduct.root 30 f 2) β η 1 • SmallLevelOriginal.fourierFunction (2*m) f
    rw [realGen_1]
    exact original_two_exact (by decide : 0<30) (by decide : 2*16=30+2) (by decide) hf
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realGen 2=
      charGen (FinitenessNormalizedTwistProduct.root 30 f 2) β η 2 • SmallLevelOriginal.fourierFunction (2*m) f
    rw [realGen_2]
    exact hB
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realGen 3=
      charGen (FinitenessNormalizedTwistProduct.root 30 f 2) β η 3 • SmallLevelOriginal.fourierFunction (2*m) f
    rw [realGen_3]
    exact hW
  · change SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] realGen 4=
      charGen (FinitenessNormalizedTwistProduct.root 30 f 2) β η 4 • SmallLevelOriginal.fourierFunction (2*m) f
    rw [realGen_4]
    exact original_C_two m hm hf

theorem representatives_eigen (g : ℍ → ℂ) (m : ℕ) (δ β η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hβ : β=1 ∨ β= -1) (hη : η=1 ∨ η= -1)
    (hg : ∀ j, g ∣[((2*m:ℕ):ℤ)] realGen j=charGen δ β η j • g) :
    ∀ r, g ∣[((2*m:ℕ):ℤ)] realRep r=charRep δ β η r • g := by
  have step (r : Fin 8) (j : Fin 5)
      (hr : g ∣[((2*m:ℕ):ℤ)] realRep r=charRep δ β η r • g)
      (hz : edgeKernel r j=1 ∨ edgeKernel r j= -1) :
      g ∣[((2*m:ℕ):ℤ)] realRep (nextIndex r j)=charRep δ β η (nextIndex r j) • g := by
    have hh := congrArg (fun M : GL (Fin 2) ℝ => g ∣[((2*m:ℕ):ℤ)] M) (normalized_edge r j)
    rw [SlashAction.slash_mul,SlashAction.slash_mul,hr,
      det_one_smul _ (realGen_det j),hg,smul_smul,character_step δ β η hδ hβ hη] at hh
    rcases hz with hz|hz
    · simpa only [hz,map_one,SlashAction.slash_one] using hh.symm
    · rw [hz] at hh
      have he : g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (-1 : SL(2,ℤ))=g :=
        SmallLevelThirtySix.slash_neg_one_even g m
      rw [he] at hh
      exact hh.symm
  have h0 : g ∣[((2*m:ℕ):ℤ)] realRep 0=charRep δ β η 0 • g := by
    rw [realRep_zero,SlashAction.slash_one]
    simp [charRep]
  have h1 := step 0 1 h0 (by decide)
  have h2 := step 0 2 h0 (by decide)
  have h3 := step 1 2 h1 (by decide)
  have h4 := step 0 3 h0 (by decide)
  have h5 := step 1 3 h1 (by decide)
  have h6 := step 2 3 h2 (by decide)
  have h7 := step 3 3 h3 (by decide)
  intro r
  fin_cases r <;> assumption

theorem kernel_invariance (g : ℍ → ℂ) (m : ℕ) (δ β η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hβ : β=1 ∨ β= -1) (hη : η=1 ∨ η= -1)
    (hg : ∀ j, g ∣[((2*m:ℕ):ℤ)] realGen j=charGen δ β η j • g) (i : Fin 26) :
    g ∣[((2*m:ℕ):ℤ)] generator i=g := by
  have hr := representatives_eigen g m δ β η hδ hβ hη hg
  have he (r : Fin 8) (j : Fin 5) : g ∣[((2*m:ℕ):ℤ)] edgeKernel r j=g := by
    have hh : (g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (edgeKernel r j))
        ∣[((2*m:ℕ):ℤ)] realRep (nextIndex r j)=g ∣[((2*m:ℕ):ℤ)] realRep (nextIndex r j) := by
      rw [← SlashAction.slash_mul,← normalized_edge,SlashAction.slash_mul,hr,
        det_one_smul _ (realGen_det j),hg,smul_smul,character_step δ β η hδ hβ hη,hr]
    have hx := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] (realRep (nextIndex r j))⁻¹) hh
    change g ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (edgeKernel r j)=g
    simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using hx
  obtain ⟨r,j,h|h⟩ := generator_covered i
  · simpa only [h] using he r j
  · simpa only [h,SlashAction.slash_mul,SmallLevelThirtySix.slash_neg_one_even] using he r j

theorem original_kernel (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 (2*m) f) (i : Fin 26) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] generator i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨β,η,hβ,hη,hg⟩ := original_generators m hm hf
  exact kernel_invariance _ m _ β η (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2) hβ hη hg i

#print axioms original_generators
#print axioms representatives_eigen
#print axioms kernel_invariance
#print axioms original_kernel

end SmallLevelThirty
