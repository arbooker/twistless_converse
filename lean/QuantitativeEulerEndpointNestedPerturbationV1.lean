module

public import QuantitativeEulerEndpointBoundedActualResidualV1
public import QuantitativeHolomorphicFilterStabilityV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNestedPerturbation
open ContinuousLinearMap Polynomial QuantitativeEulerEndpointSoftUpdate
open QuantitativeEulerEndpointResidual QuantitativeHolomorphic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem contraction_norm (a : H →L[ℂ] H) (ha : 0≤a ∧ a≤1) : ‖a‖≤1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg a ha.1).mpr ha.2

theorem sandwich_difference (a b g h : H →L[ℂ] H)
    (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) (hg : ‖g‖≤1) (hh : ‖h‖≤1) :
    ‖a*g*a-b*h*b‖≤2*‖a-b‖+‖g-h‖ := by
  have hna := contraction_norm a ha
  have hnb := contraction_norm b hb
  have hs := AsymptoticObservation.sandwich_sub_norm_le a b g h hg hh
  have hea : a.adjoint=a := (isSelfAdjoint_iff').mp (IsSelfAdjoint.of_nonneg ha.1)
  have heb : b.adjoint=b := (isSelfAdjoint_iff').mp (IsSelfAdjoint.of_nonneg hb.1)
  rw [hea,heb] at hs
  change ‖a*(g*a)-b*(h*b)‖≤_ at hs
  rw [←mul_assoc,←mul_assoc] at hs
  have hprod : ‖b‖*‖a‖≤1 := (mul_le_mul hnb hna (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hsum : ‖a‖+‖b‖≤2 := by linarith
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hsum (norm_nonneg (a-b)),
    mul_le_mul_of_nonneg_right hprod (norm_nonneg (g-h))])

/-- Stability of the actual compressed retained update. Both the incoming
filter and the normalized observation Gram may change. -/
theorem update_difference (a b g h : H →L[ℂ] H)
    (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
    (hg : 0≤g ∧ g≤1) (hh : 0≤h ∧ h≤1) (d : ℕ) :
    ‖update a (a*g*a) d-update b (b*h*b) d‖≤
      (3+2*(d:ℝ))*‖a-b‖+(d:ℝ)*‖g-h‖ := by
  have hcg : 0≤a*g*a ∧ a*g*a≤1 := by
    simpa only [inv_one,one_smul] using compressed_energy_order a g ha.1 ha.2 hg.1
      (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using hg.2)
  have hch : 0≤b*h*b ∧ b*h*b≤1 := by
    simpa only [inv_one,one_smul] using compressed_energy_order b h hb.1 hb.2 hh.1
      (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using hh.2)
  have hD (c : H →L[ℂ] H) (hc : 0≤c ∧ c≤1) :
      0≤1-(1-c)^d ∧ 1-(1-c)^d≤1 := by
    have hn : 0≤1-c := sub_nonneg.mpr hc.2
    have hu : 1-c≤1 := sub_le_self _ hc.1
    exact ⟨sub_nonneg.mpr (by simpa only [pow_zero] using CStarAlgebra.pow_antitone hu hn (Nat.zero_le d)),
      sub_le_self _ (CStarAlgebra.pow_nonneg _ _ hn)⟩
  have hng := contraction_norm (1-a*g*a) ⟨sub_nonneg.mpr hcg.2,sub_le_self _ hcg.1⟩
  have hnh := contraction_norm (1-b*h*b) ⟨sub_nonneg.mpr hch.2,sub_le_self _ hch.1⟩
  have hp := AsymptoticReconstruction.power_difference_norm_le (1-a*g*a) (1-b*h*b) hng hnh d
  have hc := sandwich_difference a b g h ha hb (contraction_norm g hg) (contraction_norm h hh)
  have he : ‖(1-a*g*a)-(1-b*h*b)‖=‖a*g*a-b*h*b‖ := by
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
  rw [he] at hp
  have hd : ‖(1-(1-a*g*a)^d)-(1-(1-b*h*b)^d)‖≤
      (d:ℝ)*(2*‖a-b‖+‖g-h‖) := by
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
    exact hp.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg d))
  have hs := sandwich_difference a b (1-(1-a*g*a)^d) (1-(1-b*h*b)^d) ha hb
    (contraction_norm _ (hD _ hcg)) (contraction_norm _ (hD _ hch))
  have hid : update a (a*g*a) d-update b (b*h*b) d=
      (a-b)-(a*(1-(1-a*g*a)^d)*a-b*(1-(1-b*h*b)^d)*b) := by
    unfold QuantitativeEulerEndpointSoftUpdate.update
    abel
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith)

theorem sharpened_difference (a b g h : H →L[ℂ] H)
    (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1)
    (hg : 0≤g ∧ g≤1) (hh : 0≤h ∧ h≤1) (d : ℕ) (q : ℝ[X]) :
    ‖aeval (update a (a*g*a) d) q-aeval (update b (b*h*b) d) q‖≤
      slopeMass q*((3+2*(d:ℝ))*‖a-b‖+(d:ℝ)*‖g-h‖) := by
  have hn (a g : H →L[ℂ] H) (ha : 0≤a ∧ a≤1) (hg : 0≤g ∧ g≤1) :
      ‖update a (a*g*a) d‖≤1 := by
    have hc : 0≤a*g*a ∧ a*g*a≤1 := by
      simpa only [inv_one,one_smul] using compressed_energy_order a g ha.1 ha.2 hg.1
        (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using hg.2)
    have hu := update_order a (a*g*a) ha.1 ha.2 hc.1 hc.2 d
    exact contraction_norm _ ⟨hu.1,hu.2.trans ha.2⟩
  have hp := polynomial_aeval_difference_norm_le q _ _ (le_refl (1:ℝ)) (hn a g ha hg) (hn b h hb hh)
  simp only [polynomialSensitivity,one_pow,mul_one] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (update_difference a b g h ha hb hg hh d) (slopeMass_nonneg q))

#print axioms sandwich_difference
#print axioms update_difference
#print axioms sharpened_difference
end QuantitativeEulerEndpointNestedPerturbation
