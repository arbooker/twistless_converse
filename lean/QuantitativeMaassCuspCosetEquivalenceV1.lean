module

public import QuantitativeMaassCuspCosetClassificationV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix
open scoped Matrix MatrixGroups

namespace QuantitativeMaass

/-- Actual integral principal-congruence left equivalence. -/
def CuspLeftEquivalent (N : ℕ) (M C : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ γ : SL(2,ℤ), γ.val.map (Int.castRingHom (ZMod N))=1 ∧ M=γ.val*C

theorem sl_inv_mul (s : SL(2,ℤ)) : (s⁻¹).val*s.val=1 := by
  rw [←SpecialLinearGroup.coe_mul,inv_mul_cancel,SpecialLinearGroup.coe_one]

theorem sl_mul_inv (s : SL(2,ℤ)) : s.val*(s⁻¹).val=1 := by
  rw [←SpecialLinearGroup.coe_mul,mul_inv_cancel,SpecialLinearGroup.coe_one]

namespace CuspLeftEquivalent

theorem refl (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : CuspLeftEquivalent N M M := by
  refine ⟨1,?_,?_⟩ <;> simp

theorem symm {N : ℕ} {M C : Matrix (Fin 2) (Fin 2) ℤ}
    (h : CuspLeftEquivalent N M C) : CuspLeftEquivalent N C M := by
  obtain ⟨γ,hγ,hM⟩ := h
  refine ⟨γ⁻¹,?_,?_⟩
  · have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ =>
        A.map (Int.castRingHom (ZMod N))) (sl_inv_mul γ)
    rw [Matrix.map_mul,hγ,mul_one] at he
    simpa using he
  · rw [hM,←mul_assoc]
    rw [sl_inv_mul,one_mul]

theorem trans {N : ℕ} {M C D : Matrix (Fin 2) (Fin 2) ℤ}
    (h : CuspLeftEquivalent N M C) (k : CuspLeftEquivalent N C D) :
    CuspLeftEquivalent N M D := by
  obtain ⟨γ,hγ,hM⟩ := h
  obtain ⟨δ,hδ,hC⟩ := k
  refine ⟨γ*δ,?_,?_⟩
  · change (γ.val*δ.val).map (Int.castRingHom (ZMod N))=1
    rw [Matrix.map_mul,hγ,hδ,mul_one]
  · change M=(γ.val*δ.val)*D
    rw [hM,hC,mul_assoc]

/-- Conjugating by any integral cusp chart preserves principal-congruence
left equivalence, since the principal congruence subgroup is normal. -/
theorem conjugate {N : ℕ} {M C : Matrix (Fin 2) (Fin 2) ℤ}
    (h : CuspLeftEquivalent N M C) (s : SL(2,ℤ)) :
    CuspLeftEquivalent N (s.val*M*s⁻¹.val) (s.val*C*s⁻¹.val) := by
  obtain ⟨γ,hγ,hM⟩ := h
  refine ⟨s*γ*s⁻¹,?_,?_⟩
  · change ((s.val*γ.val)*s⁻¹.val).map (Int.castRingHom (ZMod N))=1
    rw [Matrix.map_mul,Matrix.map_mul,hγ,mul_one,←Matrix.map_mul]
    rw [sl_mul_inv]
    simp
  · change s.val*M*s⁻¹.val=(s.val*γ.val*s⁻¹.val)*(s.val*C*s⁻¹.val)
    rw [hM]
    simp only [mul_assoc]
    rw [←mul_assoc (s⁻¹).val s.val,sl_inv_mul,one_mul]

end CuspLeftEquivalent

/-- No two of the explicit p+1 representatives are equivalent. -/
theorem cuspBranch_equivalent_iff (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1) (j k : Option (ZMod p)) :
    CuspLeftEquivalent N (cuspBranch N p j) (cuspBranch N p k) ↔ j=k := by
  constructor
  · intro hk
    obtain ⟨i,_,hi⟩ := unique_cusp_coset N p hNp hpN (cuspBranch N p j)
      (cuspBranch_det N p j) (cuspBranch_mod_level N p hpN j)
    exact (hi j (CuspLeftEquivalent.refl N _)).trans (hi k hk).symm
  · rintro rfl
    exact CuspLeftEquivalent.refl N _

#print axioms cuspBranch_equivalent_iff
#print axioms CuspLeftEquivalent.conjugate

end QuantitativeMaass
