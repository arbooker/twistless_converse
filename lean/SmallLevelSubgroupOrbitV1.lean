module

public import SmallLevelTwoThreeFourGeneratorsV1
public import SmallLevelFrickeGeneratorsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelGenerators

open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm

/-- Matrices transporting all orbit functions form a subgroup. Restricting
the orbit index to H lets a character be defined only where it is needed. -/
def orbitSubgroup (H : Subgroup SL(2,ℤ)) (k : ℤ) (w : SL(2,ℤ) → ℍ → ℂ) :
    Subgroup SL(2,ℤ) where
  carrier := {γ | γ∈H ∧ ∀ A, A∈H → w A ∣[k] γ=w (A*γ)}
  one_mem' := by simp
  mul_mem' := by
    rintro γ δ ⟨hγ,ihγ⟩ ⟨hδ,ihδ⟩
    refine ⟨H.mul_mem hγ hδ,fun A hA => ?_⟩
    rw [SlashAction.slash_mul, ihγ A hA, ihδ (A*γ) (H.mul_mem hA hγ), mul_assoc]
  inv_mem' := by
    rintro γ ⟨hγ,ih⟩
    refine ⟨H.inv_mem hγ,fun A hA => ?_⟩
    have hh := congrArg (fun F : ℍ → ℂ => F ∣[k] γ⁻¹)
      (ih (A*γ⁻¹) (H.mul_mem hA (H.inv_mem hγ)))
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      mul_assoc, inv_mul_cancel, mul_one] using hh.symm

theorem three_orbit_lift (k : ℤ) (w : SL(2,ℤ) → ℍ → ℂ)
    (hT : ∀ A, A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] T=w (A*T))
    (hU : ∀ A, A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] lower 3=w (A*lower 3))
    (hZ : ∀ A, A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] (-1 : SL(2,ℤ))=w (A*(-1)))
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 3) :
    ∀ A, A∈CongruenceSubgroup.Gamma0 3 → w A ∣[k] γ=w (A*γ) := by
  exact (gamma0_3_mem (orbitSubgroup (CongruenceSubgroup.Gamma0 3) k w)
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hT⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hU⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hZ⟩ γ hγ).2

theorem four_orbit_lift (k : ℤ) (w : SL(2,ℤ) → ℍ → ℂ)
    (hT : ∀ A, A∈CongruenceSubgroup.Gamma0 4 → w A ∣[k] T=w (A*T))
    (hU : ∀ A, A∈CongruenceSubgroup.Gamma0 4 → w A ∣[k] lower 4=w (A*lower 4))
    (hZ : ∀ A, A∈CongruenceSubgroup.Gamma0 4 → w A ∣[k] (-1 : SL(2,ℤ))=w (A*(-1)))
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 4) :
    ∀ A, A∈CongruenceSubgroup.Gamma0 4 → w A ∣[k] γ=w (A*γ) := by
  exact (gamma0_4_mem (orbitSubgroup (CongruenceSubgroup.Gamma0 4) k w)
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hT⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hU⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hZ⟩ γ hγ).2

#print axioms three_orbit_lift
#print axioms four_orbit_lift

end SmallLevelGenerators
