module

public import QuantitativeMaassExactAtkinLabelV1
public import QuantitativeMaassFiniteNormalizerCoverV1
public import QuantitativeMaassNormalizerRangeV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped MatrixGroups

namespace QuantitativeMaass

/-- At a squarefree level the finite normalizer cover is constructed from
actual integral congruence cosets and explicit Atkin--Lehner matrices. -/
theorem squarefree_normalizer_height_cover (N : ℕ) (hN : 0<N) (hS : Squarefree N) :
    ∃ g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group,
      (∀ q,∀ a∈gamma N,g q*a*(g q)⁻¹∈gamma N) ∧
      (∀ q,∀ a∈gamma N,(g q)⁻¹*a*g q∈gamma N) ∧
      ∃ Y : ℝ,0<Y ∧ ∀ z : ℍ,∃ q,∃ a : gamma N,Y≤(a.val • (g q • z)).im := by
  classical
  have h (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      ∃ g : AsymptoticRationalGroup.Group,∃ b : gamma N,∃ C : ℝ,
        0<C ∧ (∀ a∈gamma N,g*a*g⁻¹∈gamma N) ∧
        (∀ a∈gamma N,g⁻¹*a*g∈gamma N) ∧
        ∀ z : ℍ,((b.val*g*(integralLabel q.out)⁻¹) • z).im=C*z.im := by
    obtain ⟨D,Q,A,B,b,hQD,hQ,hAB,hb,hzero⟩ := squarefree_cusp_atkin_matrix N hN hS q.out⁻¹
    have hD : 0<D := by
      apply Nat.pos_of_ne_zero
      intro hDz
      have hz : N=0 := by simpa only [hDz,mul_zero] using hQD.symm
      exact hN.ne' hz
    obtain ⟨C,hC,hh⟩ := exactAtkin_cusp_height D Q hQ A B hAB q.out⁻¹ b hzero
    have hn := exactAtkinLabel_normalizes D Q hD hQ A B hAB
    refine ⟨exactAtkinLabel D Q hQ A B hAB,⟨integralLabel b,⟨b,hb,rfl⟩⟩,C,hC,?_,?_,?_⟩
    · simpa only [hQD] using hn.1
    · simpa only [hQD] using hn.2
    · intro z
      simpa only [map_inv] using hh z
  choose g b C hC hc hci hh using h
  exact ⟨g,hc,hci,finite_normalizer_height_cover N hN g b C hC hc hh⟩

/-- Consequently some finite family of actual Atkin--Lehner normalizers
gives a closed weighted cylinder embedding for every modulus-one sector.
The identification of a chosen automorphic new/sign space with these
sector equations is separate from this geometric statement. -/
theorem squarefree_normalizer_sector_closed (N : ℕ) (hN : 0<N) (hS : Squarefree N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ∃ g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group,
      ∀ χ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ,(∀ q,‖χ q‖=1) →
      Function.Injective (normalizerWeightedEmbedding N hε hv g χ) ∧
        IsClosed (Set.range (normalizerWeightedEmbedding N hε hv g χ)) := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨g,hc,hci,Y,hY,hcover⟩ := squarefree_normalizer_height_cover N hN hS
  exact ⟨g,fun χ hχ => normalizerWeightedEmbedding_closed N hε hY hv g χ hχ hc hci hcover⟩

#print axioms squarefree_normalizer_height_cover
#print axioms squarefree_normalizer_sector_closed

end QuantitativeMaass
