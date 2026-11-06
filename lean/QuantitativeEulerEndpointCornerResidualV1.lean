module

public import QuantitativeEulerEndpointPolynomialResidualV1
public import QuantitativeEulerEndpointPhysicalCornerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointResidual
open Polynomial QuantitativeEulerEndpointUpdateExpression

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- One actual band update tolerates nonzero row energies. -/
theorem corner_update_residual (P a g E : A) (hP : ‖P‖≤1) (ha : ‖a‖≤1)
    (hg : ‖g‖≤1) (hD : ‖P-a*g*a‖≤1) (hPE : P*E=E) (n : ℕ) :
    ‖cornerUpdate P a g n*E-E‖≤(3+(n:ℝ))*‖a*E-E‖+(n:ℝ)*‖g*E‖ := by
  let c := a*g*a
  let D := P-c
  let B := P-D^n*P
  have hpow (j : ℕ) : ‖D^j*P‖≤1 := by
    induction j with
    | zero => simpa only [pow_zero,one_mul] using hP
    | succ j ih =>
      rw [pow_succ',mul_assoc]
      exact (mul_contract D _ hD).trans ih
  have hB : ‖B‖≤2 := (norm_sub_le _ _).trans (by linarith [hpow n])
  have hc : ‖c*E‖≤‖a*E-E‖+‖g*E‖ := by
    have he : c*E=a*(g*(a*E-E))+a*(g*E) := by dsimp [c]; noncomm_ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add
      ((mul_contract a _ ha).trans (mul_contract g _ hg)) (mul_contract a _ ha))
  have hBE : ‖B*E‖≤(n:ℝ)*‖c*E‖ := by
    have he : D*E-E=-(c*E) := by dsimp [D]; rw [sub_mul,hPE]; abel
    have hh := power_residual D E 1 hD (by norm_num) n
    simp only [one_pow,one_smul,he,norm_neg] at hh
    have hb : B*E=E-D^n*E := by dsimp [B]; rw [sub_mul,hPE,mul_assoc,hPE]
    rw [hb,norm_sub_rev]
    exact hh
  have he : cornerUpdate P a g n*E-E=(a*E-E)-a*(B*(a*E-E)+B*E) := by
    dsimp [cornerUpdate,B,D,c]
    noncomm_ring
  rw [he]
  have hh : ‖(a*E-E)-a*(B*(a*E-E)+B*E)‖≤
      ‖a*E-E‖+(2*‖a*E-E‖+(n:ℝ)*‖c*E‖) := (norm_sub_le _ _).trans (add_le_add le_rfl
    ((mul_contract a _ ha).trans ((norm_add_le _ _).trans
      (add_le_add ((norm_mul_le B _).trans
        (mul_le_mul_of_nonneg_right hB (norm_nonneg _))) hBE))))
  have hcn := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n : (0:ℝ)≤n)
  nlinarith

end QuantitativeEulerEndpointResidual
namespace QuantitativeEulerEndpointPhysicalCorner
open Polynomial QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointBernstein
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (P : A) (hP : IsStarProjection P)

include hP in
/-- The actual complementary energy is a contraction in the ambient algebra. -/
theorem compressed_complement_order (a g : A) (hal : P*a=a) (har : a*P=a)
    (hgl : P*g=g) (hgr : g*P=g) (ha0 : 0≤a) (ha1 : a≤1) (hg0 : 0≤g) (hg1 : g≤1) :
    0≤P-a*g*a ∧ P-a*g*a≤P := by
  let a' := lift P hP a hal har
  let g' := lift P hP g hgl hgr
  have ha' := lift_order P hP a hal har ha0 ha1
  have hg' := lift_order P hP g hgl hgr hg0 hg1
  have hc : 0≤a'*g'*a' ∧ a'*g'*a'≤1 := by
    simpa only [inv_one,one_smul] using QuantitativeEulerEndpointSoftUpdate.compressed_energy_order
      a' g' ha'.1 ha'.2 hg'.1 (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using hg'.2)
  have hc0 : (0:A)≤a*g*a := (coe_le_iff P hP 0 (a'*g'*a')).mpr hc.1
  have hc1 : a*g*a≤P := (coe_le_iff P hP (a'*g'*a') 1).mpr hc.2
  exact ⟨sub_nonneg.mpr hc1,sub_le_self _ hc0⟩

include hP in
theorem corner_update_order (a g : A) (hal : P*a=a) (har : a*P=a)
    (hgl : P*g=g) (hgr : g*P=g) (ha0 : 0≤a) (ha1 : a≤1) (hg0 : 0≤g) (hg1 : g≤1)
    (n : ℕ) : 0≤cornerUpdate P a g n ∧ cornerUpdate P a g n≤a := by
  have hx : ScalarSharpening (X : ℝ[X]) := by
    refine ⟨by simp,by simp,?_⟩
    intro x
    simpa only [eval_X] using (show 0≤(x:ℝ) ∧ (x:ℝ)≤x from ⟨x.property.1,le_rfl⟩)
  have h := sharpened_order P hP a g hal har hgl hgr ha0 ha1 hg0 hg1 n hx
  have hu : cornerUpdate P a g n*P=cornerUpdate P a g n := by
    have hh := coe_update P hP (lift P hP a hal har) (lift P hP g hgl hgr) n
    have hs := (coe_support P hP
      (QuantitativeEulerEndpointSoftUpdate.update (lift P hP a hal har)
        (lift P hP a hal har*lift P hP g hgl hgr*lift P hP a hal har) n)).2
    rw [hh] at hs
    exact hs
  simp only [aeval_X,hu] at h
  exact ⟨h.1,h.2.1⟩

#print axioms compressed_complement_order
#print axioms corner_update_order
end QuantitativeEulerEndpointPhysicalCorner
