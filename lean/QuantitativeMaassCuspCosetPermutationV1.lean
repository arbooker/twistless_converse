module

public import QuantitativeMaassCuspCosetEquivalenceV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix
open scoped Matrix MatrixGroups

namespace QuantitativeMaass

def cuspConjugate (s : SL(2,ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ := s.val*M*(s⁻¹).val

theorem cuspConjugate_det (s : SL(2,ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (cuspConjugate s M).det=M.det := by
  unfold cuspConjugate
  rw [Matrix.det_mul,Matrix.det_mul,s.det_coe,(s⁻¹).det_coe,one_mul,mul_one]

theorem cuspConjugate_mod_level (N : ℕ) (s : SL(2,ℤ))
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.map (Int.castRingHom (ZMod N))=1) :
    (cuspConjugate s M).map (Int.castRingHom (ZMod N))=1 := by
  simp only [cuspConjugate,Matrix.map_mul,hM,mul_one]
  rw [←Matrix.map_mul]
  rw [sl_mul_inv]
  simp

theorem cuspConjugate_inverse (s : SL(2,ℤ)) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    cuspConjugate s⁻¹ (cuspConjugate s M)=M := by
  simp only [cuspConjugate,inv_inv]
  rw [mul_assoc s.val M (s⁻¹).val,←mul_assoc (s⁻¹).val s.val,sl_inv_mul,one_mul]
  rw [mul_assoc,sl_inv_mul,mul_one]

theorem unique_conjugated_cusp_coset (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (j : Option (ZMod p)) :
    ∃! k : Option (ZMod p), CuspLeftEquivalent N
      (cuspConjugate s (cuspBranch N p j)) (cuspBranch N p k) := by
  apply unique_cusp_coset N p hNp hpN
  · rw [cuspConjugate_det,cuspBranch_det]
  · exact cuspConjugate_mod_level N s _ (cuspBranch_mod_level N p hpN j)

def cuspCosetIndex (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (j : Option (ZMod p)) : Option (ZMod p) :=
  Classical.choose (unique_conjugated_cusp_coset N p hNp hpN s j)

theorem cuspCosetIndex_spec (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (j : Option (ZMod p)) : CuspLeftEquivalent N
      (cuspConjugate s (cuspBranch N p j))
      (cuspBranch N p (cuspCosetIndex N p hNp hpN s j)) :=
  (Classical.choose_spec (unique_conjugated_cusp_coset N p hNp hpN s j)).1

theorem cuspCosetIndex_injective (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1) (s : SL(2,ℤ)) :
    Function.Injective (cuspCosetIndex N p hNp hpN s) := by
  intro j k he
  have hj := cuspCosetIndex_spec N p hNp hpN s j
  have hk := cuspCosetIndex_spec N p hNp hpN s k
  rw [he] at hj
  have h := (hj.trans hk.symm).conjugate s⁻¹
  change CuspLeftEquivalent N (cuspConjugate s⁻¹ (cuspConjugate s (cuspBranch N p j)))
    (cuspConjugate s⁻¹ (cuspConjugate s (cuspBranch N p k))) at h
  rw [cuspConjugate_inverse,cuspConjugate_inverse] at h
  exact (cuspBranch_equivalent_iff N p hNp hpN j k).mp h

/-- An actual permutation of the p+1 unramified branches under every
integral cusp chart, with principal-congruence left factors. -/
def cuspCosetPermutation (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1) (s : SL(2,ℤ)) :
    Equiv.Perm (Option (ZMod p)) :=
  Equiv.ofBijective (cuspCosetIndex N p hNp hpN s)
    ((Finite.injective_iff_bijective).mp (cuspCosetIndex_injective N p hNp hpN s))

theorem cuspCosetPermutation_spec (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (j : Option (ZMod p)) : CuspLeftEquivalent N
      (cuspConjugate s (cuspBranch N p j))
      (cuspBranch N p (cuspCosetPermutation N p hNp hpN s j)) :=
  cuspCosetIndex_spec N p hNp hpN s j

#print axioms cuspCosetPermutation_spec

end QuantitativeMaass
