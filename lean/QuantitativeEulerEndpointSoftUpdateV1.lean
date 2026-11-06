module

public import QuantitativeEulerEndpointSharpenControlledV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointSoftUpdate
open Polynomial

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- A kernel-preserving polynomial update using a normalized source energy. -/
def update (A C : 𝔄) (d : ℕ) : 𝔄 := A-A*(1-(1-C)^d)*A

theorem update_order (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    (hC0 : 0≤C) (hC1 : C≤1) (d : ℕ) : 0≤update A C d ∧ update A C d≤A := by
  have hD0 : 0≤1-C := sub_nonneg.mpr hC1
  have hD1 : 1-C≤1 := sub_le_self _ hC0
  have hg0 : 0≤1-(1-C)^d := sub_nonneg.mpr
    (by simpa only [pow_zero] using CStarAlgebra.pow_antitone hD1 hD0 (Nat.zero_le d))
  have hg1 : 1-(1-C)^d≤1 := sub_le_self _ (CStarAlgebra.pow_nonneg _ _ hD0)
  have hconj := (IsSelfAdjoint.of_nonneg hA0).conjugate_le_conjugate hg1
  simp only [mul_one] at hconj
  have hsq := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1)
  exact ⟨sub_nonneg.mpr (hconj.trans hsq),sub_le_self _ (conjugate_nonneg_of_nonneg hg0 hA0)⟩

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem update_fixed (A C E : 𝔄) (hAE : A*E=E) (hCE : C*E=0) (d : ℕ) :
    update A C d*E=E := by
  have hDE : (1-C)*E=E := by rw [sub_mul,one_mul,hCE,sub_zero]
  have hp (n : ℕ) : (1-C)^n*E=E := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,mul_assoc,hDE,ih]
  simp only [update,sub_mul,mul_assoc,hAE,one_mul,hp,sub_self,mul_zero,sub_zero]

/-- Compressing a bounded positive residual energy by a positive
contraction gives the normalized positive contraction used by update. -/
theorem compressed_energy_order (A G : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    (hG0 : 0≤G) {K : ℝ} (hK : 0<K) (hGK : G≤K • (1:𝔄)) :
    0≤K⁻¹ • (A*G*A) ∧ K⁻¹ • (A*G*A)≤1 := by
  have hAA := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1)
  have hconj := (IsSelfAdjoint.of_nonneg hA0).conjugate_le_conjugate hGK
  have he : A*(K • (1:𝔄))*A=K • (A*A) := by simp only [mul_smul_comm,smul_mul_assoc,mul_one]
  rw [he] at hconj
  have hh := (smul_le_smul_of_nonneg_left hconj (inv_nonneg.mpr hK.le)).trans
    (smul_le_smul_of_nonneg_left (smul_le_smul_of_nonneg_left (hAA.trans hA1) hK.le)
      (inv_nonneg.mpr hK.le))
  simp only [smul_smul,inv_mul_cancel₀ hK.ne',one_smul] at hh
  exact ⟨smul_nonneg (inv_nonneg.mpr hK.le) (conjugate_nonneg_of_nonneg hG0 hA0),hh⟩

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem compressed_energy_kills (A G E : 𝔄) (hAE : A*E=E) (hGE : G*E=0) (K : ℝ) :
    (K⁻¹ • (A*G*A))*E=0 := by simp only [smul_mul_assoc,mul_assoc,hAE,hGE,mul_zero,smul_zero]

/-- One complete polynomial update and sharpening step. It is order
 decreasing, has small trace defect, and retains every exact fixed solution.
This theorem does not yet assert the block's quantitative trace contraction. -/
theorem exists_sharpened_update (τ : 𝔄 →L[ℝ] ℝ) (hτ : Monotone τ)
    (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hC1 : C≤1)
    (d : ℕ) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧
      (∑ i∈p.support, |p.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      0≤aeval (update A C d) p ∧ aeval (update A C d) p≤A ∧
      τ (aeval (update A C d) p-(aeval (update A C d) p)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, A*E=E → C*E=0 → aeval (update A C d) p*E=E) := by
  have ho := update_order A C hA0 hA1 hC0 hC1 d
  obtain ⟨p,hdeg,hmass,_hzero,hone,hp0,hp1,hdef⟩ :=
    QuantitativeEulerEndpointBernstein.exists_controlled_operator_sharpening τ hτ
      (update A C d) ho.1 (ho.2.trans hA1) hJ
  refine ⟨p,hdeg,hmass,hp0,hp1.trans ho.2,hdef,?_⟩
  intro E hAE hCE
  exact QuantitativeEulerEndpointBernstein.polynomial_preserves_fixed _ E
    (update_fixed A C E hAE hCE d) p hone

#print axioms update_order
#print axioms update_fixed
#print axioms compressed_energy_order
#print axioms compressed_energy_kills
#print axioms exists_sharpened_update
end QuantitativeEulerEndpointSoftUpdate
