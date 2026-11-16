module

public import AsymptoticCongruenceFiniteCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticHyperbolicArea
open AsymptoticCongruenceCover
open scoped MatrixGroups Pointwise

namespace QuantitativeMaass

/-- A finite family of cusp-to-infinity maps gives a uniform positive
height bound on every orbit. The height constant is the minimum of the
finitely many explicit positive scaling factors. -/
theorem finite_normalizer_height_cover (N : ℕ) (hN : 0<N)
    (g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group)
    (b : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → gamma N)
    (C : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℝ)
    (hC : ∀ q,0<C q)
    (hc : ∀ q,∀ a∈gamma N,g q*a*(g q)⁻¹∈gamma N)
    (hheight : ∀ q,∀ z : ℍ,
      (((b q).val*g q*(integralLabel q.out)⁻¹) • z).im=C q*z.im) :
    ∃ Y : ℝ,0<Y ∧ ∀ z : ℍ,∃ q,∃ a : gamma N,Y≤(a.val • (g q • z)).im := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  let C₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty C
  have hC₀ : 0<C₀ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun q _ => hC q)
  have hle (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : C₀≤C q :=
    Finset.inf'_le _ (Finset.mem_univ q)
  refine ⟨C₀/4,by positivity,?_⟩
  intro z
  obtain ⟨h,hh⟩ := orbit_meets_cover N z
  obtain ⟨q,w,hw,he⟩ := mem_iUnion.mp hh
  let a : gamma N := ⟨(b q).val*(g q*h.val*(g q)⁻¹),
    (gamma N).mul_mem (b q).property (hc q h.val h.property)⟩
  refine ⟨q,a,?_⟩
  have heq : a.val • (g q • z)=((b q).val*g q*(integralLabel q.out)⁻¹) • w := by
    change ((b q).val*(g q*h.val*(g q)⁻¹)) • (g q • z)=_
    simp only [mul_smul,inv_smul_smul]
    change (integralLabel q.out)⁻¹ • w=h.val • z at he
    rw [he]
  rw [heq,hheight]
  have hwim : (1:ℝ)/4<w.im := hw.2
  calc
    C₀/4≤C q/4 := div_le_div_of_nonneg_right (hle q) (by norm_num)
    _≤C q*w.im := by nlinarith [hC q]

#print axioms finite_normalizer_height_cover

end QuantitativeMaass
