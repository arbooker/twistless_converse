module

public import QuantitativeMaassAdmissibleCuspReductionV1
public import QuantitativeMaassSquarefreeNormalizerCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped MatrixGroups

namespace QuantitativeMaass

theorem admissible_normalizer_cusp_transport (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (a : SL(2,ℤ)) :
    ∃ g : AsymptoticRationalGroup.Group,
      (∀ x∈gamma N,g*x*g⁻¹∈gamma N) ∧ (∀ x∈gamma N,g⁻¹*x*g∈gamma N) ∧
      ∃ b : gamma N,∃ C : ℝ,0<C ∧ ∀ z : ℍ,
        ((b.val*g*integralLabel a) • z).im=C*z.im := by
  obtain ⟨g,hg,hgi,a',hfull,d,hd,he⟩ := admissible_cusp_reduction N hN a
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
  refine ⟨u*g,?_,?_,⟨integralLabel b,⟨b,hb,rfl⟩⟩,C*d,mul_pos hC (by exact_mod_cast hd),?_⟩
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
theorem admissible_normalizer_height_cover (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∃ g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group,
      (∀ q,∀ a∈gamma N,g q*a*(g q)⁻¹∈gamma N) ∧
      (∀ q,∀ a∈gamma N,(g q)⁻¹*a*g q∈gamma N) ∧
      ∃ Y : ℝ,0<Y ∧ ∀ z : ℍ,∃ q,∃ a : gamma N,Y≤(a.val • (g q • z)).im := by
  classical
  have h (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    admissible_normalizer_cusp_transport N hN q.out⁻¹
  choose g hc hci b C hC hh using h
  have hheight : ∀ q,∀ z : ℍ,
      (((b q).val*g q*(integralLabel q.out)⁻¹) • z).im=C q*z.im := by
    intro q z
    simpa only [map_inv] using hh q z
  exact ⟨g,hc,hci,finite_normalizer_height_cover N hN.1 g b C hC hc hheight⟩

theorem admissible_normalizer_sector_closed (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ∃ g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group,
      ∀ χ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ,(∀ q,‖χ q‖=1) →
      Function.Injective (normalizerWeightedEmbedding N hε hv g χ) ∧
        IsClosed (Set.range (normalizerWeightedEmbedding N hε hv g χ)) := by
  classical
  let : NeZero N := ⟨hN.1.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨g,hc,hci,Y,hY,hcover⟩ := admissible_normalizer_height_cover N hN
  exact ⟨g,fun χ hχ => normalizerWeightedEmbedding_closed N hε hY hv g χ hχ hc hci hcover⟩

#print axioms admissible_normalizer_cusp_transport
#print axioms admissible_normalizer_height_cover
#print axioms admissible_normalizer_sector_closed

end QuantitativeMaass
