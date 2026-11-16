module

public import QuantitativeMaassCuspCosetIntegralV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix
open scoped Matrix MatrixGroups

namespace QuantitativeMaass

theorem determinant_prime_mod_nonzero (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det=p) :
    M.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd (i j : Fin 2) : (p:ℤ) ∣ M i j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod p) => A i j) hz
  obtain ⟨a,ha⟩ := hd 0 0
  obtain ⟨b,hb⟩ := hd 0 1
  obtain ⟨c,hc⟩ := hd 1 0
  obtain ⟨d,he⟩ := hd 1 1
  have hpZ : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdiv : (p:ℤ) ∣ 1 := by
    refine ⟨a*d-b*c,?_⟩
    apply mul_left_cancel₀ hpZ
    rw [Matrix.det_fin_two,ha,hb,hc,he] at hdet
    linear_combination -hdet
  exact (Fact.out : p.Prime).not_dvd_one (by exact_mod_cast hdiv)

/-- Every determinant-p matrix congruent to I modulo N has one and only
one of the p+1 actual unramified principal-congruence cosets. The integral
left factor and its congruence are both constructed. -/
theorem unique_cusp_coset (N p : ℕ) [Fact p.Prime]
    (hNp : (N : ZMod p)≠0) (hpN : (p : ZMod N)=1)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det=p)
    (hlevel : M.map (Int.castRingHom (ZMod N))=1) :
    ∃! j : Option (ZMod p), ∃ γ : SL(2,ℤ),
      γ.val.map (Int.castRingHom (ZMod N))=1 ∧ M=γ.val*cuspBranch N p j := by
  let a : ZMod p := M 0 0
  let b : ZMod p := M 0 1
  let c : ZMod p := M 1 0
  let d : ZMod p := M 1 1
  have hshape : M.map (Int.castRingHom (ZMod p)) = !![a,b;c,d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hprim : ¬(a=0 ∧ b=0 ∧ c=0 ∧ d=0) := by
    rintro ⟨ha,hb,hc,hd⟩
    apply determinant_prime_mod_nonzero p M hdet
    rw [hshape,ha,hb,hc,hd]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hzero : a*d-b*c=0 := by
    have hh := congrArg (Int.castRingHom (ZMod p)) hdet
    change ((M.det : ℤ) : ZMod p) = ((p:ℤ):ZMod p) at hh
    simpa [Matrix.det_fin_two,a,b,c,d] using hh
  obtain ⟨j,hj,hunique⟩ := cuspAdjMod_unique (N : ZMod p) a b c d hNp hprim hzero
  have hcast : (M*(cuspBranch N p j).adjugate).map (Int.castRingHom (ZMod p))=0 := by
    rw [Matrix.map_mul,cuspBranch_adjugate_mod,hshape]
    exact hj
  have hdiv (i k : Fin 2) : (p:ℤ) ∣ (M*(cuspBranch N p j).adjugate) i k := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    exact congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod p) => A i k) hcast
  obtain ⟨γ,hγ,he⟩ := exists_integral_left_quotient p (Fact.out : p.Prime).ne_zero
    M (cuspBranch N p j) hdet (cuspBranch_det N p j) hdiv
  refine ⟨j,⟨γ,left_quotient_mod_level N p hpN M (cuspBranch N p j) hlevel
    (cuspBranch_mod_level N p hpN j) γ he,hγ⟩,?_⟩
  rintro k ⟨δ,_,hδ⟩
  apply hunique k
  have hm : M*(cuspBranch N p k).adjugate=(p:ℤ) • δ.val := by
    rw [hδ,mul_assoc,Matrix.mul_adjugate,cuspBranch_det,mul_smul_comm,mul_one]
  have hz : (M*(cuspBranch N p k).adjugate).map (Int.castRingHom (ZMod p))=0 := by
    rw [hm]
    ext i l
    change (((p:ℤ)*δ.val i l : ℤ):ZMod p)=0
    simp
  rw [Matrix.map_mul,cuspBranch_adjugate_mod,hshape] at hz
  exact hz

#print axioms determinant_prime_mod_nonzero
#print axioms unique_cusp_coset

end QuantitativeMaass
