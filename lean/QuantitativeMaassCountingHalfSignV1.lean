module

public import QuantitativeNewGapSectorIncidenceV1
public import QuantitativeMaassRegularCoverMetricV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticIntegralSubgroup AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticFreshMatrices
open AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.CountingMetric

/-- The repeated dyadic original row forces half-translation anti-invariance
in the actual counting new/sign sector. No analytic representative is needed. -/
theorem countingSector_half (N : ℕ) (hN : 0<N) (h4 : 4∣N) (e : Sector N)
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (g : AsymptoticRationalGroup.Group) :
    f (classOf (gamma N) (translationLabel (1/2)*g))= -f (classOf (gamma N) g) := by
  let z : UpperHalfPlane := ⟨Complex.I,by simp⟩
  have hi := (AsymptoticQuotientIncidence.induction_mem_space N hN
    (by norm_num : (0:ℝ)<1) (by omega : 1≤(1:ℕ)) e z f).mp
    (countingSector_induction_mem_incidence N hN e
      (by norm_num : (0:ℝ)<1) (by omega : 1≤(1:ℕ)) z f hf)
  have h2 : 2∣N := (by decide : 2∣4).trans h4
  have hh := hi.2 ⟨2,by decide,h2⟩ (dilationLabel 2 (by decide)*g)
  have hsq : 2^2∣N := by simpa only [show (2:ℕ)^2=4 by norm_num] using h4
  simp only [AsymptoticCylinderRamified.eigenvalue,ite_eq_left hsq,zero_mul] at hh
  simp only [←mul_assoc,AsymptoticOrbitDecode.ramifiedLabel_mul_dilation,
    Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,
    zero_div,AsymptoticRamifiedTwistedLaw.translationLabel_zero,one_mul] at hh
  exact eq_neg_of_add_eq_zero_right hh

/-- Pointwise modulus stabilizers form a subgroup even before imposing
normalizer membership. -/
def modulusStabilizer {G : Type*} [Group G] (f : G→ℂ) : Subgroup G where
  carrier := {a | ∀ g,‖f (a*g)‖=‖f g‖}
  one_mem' := by intro g; rw [one_mul]
  mul_mem' := by intro a b ha hb g; rw [mul_assoc,ha,hb]
  inv_mem' := by
    intro a ha g
    have hh := ha (a⁻¹*g)
    rw [mul_inv_cancel_left] at hh
    exact hh.symm

theorem gamma_le_modulusStabilizer (N : ℕ) (f : Classes (gamma N)→ℂ) :
    gamma N≤modulusStabilizer (fun g => f (classOf (gamma N) g)) := by
  intro a ha g
  exact congrArg (fun q => ‖f q‖) (classOf_mul (gamma N) ⟨a,ha⟩ g)

#print axioms countingSector_half
#print axioms gamma_le_modulusStabilizer
end QuantitativeMaass.CountingMetric
