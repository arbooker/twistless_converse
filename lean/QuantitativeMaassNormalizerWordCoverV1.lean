module

public import QuantitativeMaassNormalizerWordReductionV1
public import QuantitativeMaassSquarefreeNormalizerCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticIntegralSubgroup
open AsymptoticFreshMatrices
open scoped MatrixGroups

namespace QuantitativeMaass

theorem admissible_normalizer_cusp_transport_subgroup (N : ℕ) (hN : GridAdmissibleGap.Admissible N)

    (S : Subgroup AsymptoticRationalGroup.Group)
    (hT : 4∣N → translationLabel (1/2)∈S)
    (hW : frickeLabel N hN.1∈S)
    (hA : ∀ (D Q : ℕ) (hQ : 0<Q) (A B : ℤ) (hAB : (Q:ℤ)*A+(D:ℤ)*B=1),
      Q*D=N → exactAtkinLabel D Q hQ A B hAB∈S)
    (a : SL(2,ℤ)) :
    ∃ g : AsymptoticRationalGroup.Group,g∈S ∧
      (∀ x∈gamma N,g*x*g⁻¹∈gamma N) ∧ (∀ x∈gamma N,g⁻¹*x*g∈gamma N) ∧
      ∃ b : gamma N,∃ C : ℝ,0<C ∧ ∀ z : ℍ,
        ((b.val*g*integralLabel a) • z).im=C*z.im := by
  have hL (L : ℕ) (hp : 0<L) (he : 4*L=N) : integralLabel (lowerSL (2*L) 1)∈S := by
    apply lowerHalf_mem_of_fricke_half L hp S
    · subst N
      exact hW
    · apply hT
      exact ⟨L,he.symm⟩
  obtain ⟨g,hgS,hg,hgi,a',hfull,d,hd,he⟩ := admissible_cusp_reduction_subgroup N hN S hT hL a
  obtain ⟨D,Q,A,B,b,hQD,hQ,hAB,hb,hzero⟩ := admissible_cusp_atkin_matrix N hN a' hfull
  have hD : 0<D := by
    apply Nat.pos_of_ne_zero
    intro hDz
    have hz : N=0 := by simpa only [hDz,mul_zero] using hQD.symm
    exact hN.1.ne' hz
  let u := exactAtkinLabel D Q hQ A B hAB
  have hu : (∀ x∈gamma N,u*x*u⁻¹∈gamma N) ∧ (∀ x∈gamma N,u⁻¹*x*u∈gamma N) := by
    simpa only [hQD] using exactAtkinLabel_normalizes D Q hD hQ A B hAB
  obtain ⟨C,hC,hscale⟩ := exactAtkin_cusp_height D Q hQ A B hAB a' b hzero
  refine ⟨u*g,S.mul_mem (hA D Q hQ A B hAB hQD) hgS,?_,?_,⟨integralLabel b,⟨b,hb,rfl⟩⟩,C*d,mul_pos hC (by exact_mod_cast hd),?_⟩
  · intro x hx
    have h := hu.1 (g*x*g⁻¹) (hg x hx)
    convert h using 1; group
  · intro x hx
    have h := hgi (u⁻¹*x*u) (hu.2 x hx)
    convert h using 1; group
  · intro z
    have heq : integralLabel b*(u*g)*integralLabel a=
        (integralLabel b*u*integralLabel a')*dilationLabel d hd := by
      calc
        _=integralLabel b*u*(g*integralLabel a) := by group
        _=_ := by rw [he]; group
    change ((integralLabel b*(u*g)*integralLabel a) • z).im=(C*(d:ℝ))*z.im
    rw [heq,mul_smul]
    change ((integralLabel b*exactAtkinLabel D Q hQ A B hAB*integralLabel a') •
      (dilationLabel d hd • z)).im=_
    rw [hscale,dilationLabel_height]
    ring

/-- The finite normalizer height cover is now constructed at every
admissible level, including all dyadic exponents zero through three. -/
theorem admissible_normalizer_height_cover_subgroup (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (S : Subgroup AsymptoticRationalGroup.Group)
    (hT : 4∣N → translationLabel (1/2)∈S)
    (hW : frickeLabel N hN.1∈S)
    (hA : ∀ (D Q : ℕ) (hQ : 0<Q) (A B : ℤ) (hAB : (Q:ℤ)*A+(D:ℤ)*B=1),
      Q*D=N → exactAtkinLabel D Q hQ A B hAB∈S) :
    ∃ g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group,
      (∀ q,g q∈S) ∧ (∀ q,∀ a∈gamma N,g q*a*(g q)⁻¹∈gamma N) ∧
      (∀ q,∀ a∈gamma N,(g q)⁻¹*a*g q∈gamma N) ∧
      ∃ Y : ℝ,0<Y ∧ ∀ z : ℍ,∃ q,∃ a : gamma N,Y≤(a.val • (g q • z)).im := by
  classical
  have h (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    admissible_normalizer_cusp_transport_subgroup N hN S hT hW hA q.out⁻¹
  choose g hgS hc hci b C hC hh using h
  have hheight : ∀ q,∀ z : ℍ,
      (((b q).val*g q*(integralLabel q.out)⁻¹) • z).im=C q*z.im := by
    intro q z
    simpa only [map_inv] using hh q z
  exact ⟨g,hgS,hc,hci,finite_normalizer_height_cover N hN.1 g b C hC hc hheight⟩


#print axioms admissible_normalizer_cusp_transport_subgroup
#print axioms admissible_normalizer_height_cover_subgroup

end QuantitativeMaass
