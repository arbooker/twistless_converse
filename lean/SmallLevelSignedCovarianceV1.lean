module

public import SmallLevelSignedResiduesV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelGenerators

open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm

theorem three_signed (m : ℕ) (g : ℍ → ℂ)
    (hT : g ∣[((2*m:ℕ):ℤ)] T= -g)
    (hU : g ∣[((2*m:ℕ):ℤ)] lower 3= -g)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 3) :
    g ∣[((2*m:ℕ):ℤ)] γ=(signTwo (reduction 2 γ):ℂ) • g := by
  let w : SL(2,ℤ) → ℍ → ℂ := fun A => (signTwo (reduction 2 A):ℂ) • g
  have ht (A : SL(2,ℤ)) (_hA : A∈CongruenceSubgroup.Gamma0 3) :
      w A ∣[((2*m:ℕ):ℤ)] T=w (A*T) := by
    simp only [w, ModularForm.SL_smul_slash, hT, map_mul, signTwo_T,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hu (A : SL(2,ℤ)) (_hA : A∈CongruenceSubgroup.Gamma0 3) :
      w A ∣[((2*m:ℕ):ℤ)] lower 3=w (A*lower 3) := by
    simp only [w, ModularForm.SL_smul_slash, hU, map_mul, signTwo_U,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hz (A : SL(2,ℤ)) (_hA : A∈CongruenceSubgroup.Gamma0 3) :
      w A ∣[((2*m:ℕ):ℤ)] (-1 : SL(2,ℤ))=w (A*(-1)) := by
    simp only [w, ModularForm.SL_smul_slash, SmallLevelThirtySix.slash_neg_one_even,
      map_mul, signTwo_Z]
  have hh := three_orbit_lift ((2*m:ℕ):ℤ) w ht hu hz γ hγ 1 (Subgroup.one_mem _)
  simpa only [w, map_one, signTwo_one, Int.cast_one, one_smul, one_mul] using hh

theorem four_signed (m : ℕ) (g : ℍ → ℂ)
    (hT : g ∣[((2*m:ℕ):ℤ)] T= -g)
    (hU : g ∣[((2*m:ℕ):ℤ)] lower 4= -g)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 4) :
    g ∣[((2*m:ℕ):ℤ)] γ=(signEight (reduction 8 γ):ℂ) • g := by
  let w : SL(2,ℤ) → ℍ → ℂ := fun A => (signEight (reduction 8 A):ℂ) • g
  have ht (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 4) :
      w A ∣[((2*m:ℕ):ℤ)] T=w (A*T) := by
    simp only [w, ModularForm.SL_smul_slash, hT, map_mul,
      signEight_T _ (gamma_four_residue A hA), Int.cast_neg, _root_.neg_smul, smul_neg]
  have hu (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 4) :
      w A ∣[((2*m:ℕ):ℤ)] lower 4=w (A*lower 4) := by
    simp only [w, ModularForm.SL_smul_slash, hU, map_mul,
      signEight_U _ (gamma_four_residue A hA), Int.cast_neg, _root_.neg_smul, smul_neg]
  have hz (A : SL(2,ℤ)) (hA : A∈CongruenceSubgroup.Gamma0 4) :
      w A ∣[((2*m:ℕ):ℤ)] (-1 : SL(2,ℤ))=w (A*(-1)) := by
    simp only [w, ModularForm.SL_smul_slash, SmallLevelThirtySix.slash_neg_one_even,
      map_mul, signEight_Z _ (gamma_four_residue A hA)]
  have hh := four_orbit_lift ((2*m:ℕ):ℤ) w ht hu hz γ hγ 1 (Subgroup.one_mem _)
  simpa only [w, map_one, signEight_one, Int.cast_one, one_smul, one_mul] using hh

#print axioms three_signed
#print axioms four_signed

end SmallLevelGenerators
