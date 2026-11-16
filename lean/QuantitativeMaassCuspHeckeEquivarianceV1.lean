module

public import QuantitativeMaassCuspCosetPermutationV1
public import QuantitativeMaassCuspPeriodV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalCusp AsymptoticClassicalDiscriminant
open scoped MatrixGroups BigOperators

namespace QuantitativeMaass

def cuspBranchGL (N p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero ((cuspBranch N p j).map (Int.castRingHom ℝ)) (by
    have hm : ((cuspBranch N p j).map (Int.castRingHom ℝ)).det =
        ((cuspBranch N p j).det : ℝ) := by simp [Matrix.det_fin_two]
    rw [hm,cuspBranch_det]
    exact_mod_cast (Fact.out : p.Prime).ne_zero)

theorem cuspBranchGL_val (N p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) :
    (cuspBranchGL N p j).val=(cuspBranch N p j).map (Int.castRingHom ℝ) := rfl

theorem principal_mem_Gamma0 (N : ℕ) (γ : SL(2,ℤ))
    (hγ : γ.val.map (Int.castRingHom (ZMod N))=1) :
    γ ∈ CongruenceSubgroup.Gamma0 N := by
  apply CongruenceSubgroup.Gamma0_mem.mpr
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod N) => A 1 0) hγ
  exact hh

/-- The classified integral coset equality gives equality of the actual
real Möbius transformations, with no abstract Hecke-action hypothesis. -/
theorem cuspBranchGL_conjugate (N p : ℕ) [Fact p.Prime]
    (s γ : SL(2,ℤ)) (j k : Option (ZMod p))
    (he : cuspConjugate s (cuspBranch N p j)=γ.val*cuspBranch N p k) :
    SpecialLinearGroup.mapGL ℝ s * cuspBranchGL N p j *
      SpecialLinearGroup.mapGL ℝ s⁻¹ =
    SpecialLinearGroup.mapGL ℝ γ * cuspBranchGL N p k := by
  apply Units.ext
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ =>
    M.map (Int.castRingHom ℝ)) he
  change (s.val.map (Int.castRingHom ℝ) * (cuspBranch N p j).map (Int.castRingHom ℝ)) *
    (s⁻¹).val.map (Int.castRingHom ℝ) =
    γ.val.map (Int.castRingHom ℝ) * (cuspBranch N p k).map (Int.castRingHom ℝ)
  simpa only [cuspConjugate,Matrix.map_mul] using hh

/-- The actual finite Hecke correspondence in representatives adapted to the
common period N at every cusp. -/
def cuspHeckeSum (N p : ℕ) [Fact p.Prime] (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ j : Option (ZMod p), f (cuspBranchGL N p j • z)

/-- All integral cusp charts commute with the unramified correspondence
when p is 1 modulo N. Every principal-congruence correction is removed by
actual level-N automorphy, and the branch sum is reindexed by a proved
permutation. -/
theorem cuspHeckeSum_chart (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z) (z : ℍ) :
    cuspHeckeSum N p f (SpecialLinearGroup.mapGL ℝ s • z) =
      cuspHeckeSum N p (fun w => f (SpecialLinearGroup.mapGL ℝ s • w)) z := by
  let e := cuspCosetPermutation N p hNp hpN s⁻¹
  have he (j : Option (ZMod p)) :
      f (cuspBranchGL N p j • (SpecialLinearGroup.mapGL ℝ s • z)) =
      f (SpecialLinearGroup.mapGL ℝ s • (cuspBranchGL N p (e j) • z)) := by
    obtain ⟨γ,hγ,hj⟩ := cuspCosetPermutation_spec N p hNp hpN s⁻¹ j
    have hg := cuspBranchGL_conjugate N p s⁻¹ γ j (e j) hj
    have hg' := congrArg (fun g : GL (Fin 2) ℝ => SpecialLinearGroup.mapGL ℝ s*g) hg
    simp only [inv_inv,map_inv] at hg'
    rw [←mul_assoc,←mul_assoc,mul_inv_cancel,one_mul] at hg'
    have hd : s*γ*s⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
      apply principal_mem_Gamma0
      change (s.val*γ.val*(s⁻¹).val).map (Int.castRingHom (ZMod N))=1
      rw [Matrix.map_mul,Matrix.map_mul,hγ,mul_one,←Matrix.map_mul,sl_mul_inv]
      simp
    have hi := hinv ⟨integralLabel (s*γ*s⁻¹),⟨s*γ*s⁻¹,hd,rfl⟩⟩
      (SpecialLinearGroup.mapGL ℝ s • (cuspBranchGL N p (e j) • z))
    rw [integralLabel_action] at hi
    change f (SpecialLinearGroup.mapGL ℝ (s*γ*s⁻¹) • _) = _ at hi
    simp only [map_mul,map_inv,mul_smul,inv_smul_smul] at hi
    rw [←mul_smul,hg']
    simpa only [mul_smul] using hi
  unfold cuspHeckeSum
  simp_rw [he]
  exact Equiv.sum_comp e (fun j => f (SpecialLinearGroup.mapGL ℝ s •
    (cuspBranchGL N p j • z)))

#print axioms cuspHeckeSum_chart

end QuantitativeMaass
