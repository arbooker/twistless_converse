module

public import QuantitativeNewGapTotalWeightedV1
public import QuantitativeNewGapNewCommutationV1
public import QuantitativeArithmeticCrossPrimeV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticPolarIsometry UpperHalfPlane
open scoped lp

/-- Actual local-new projections commute at every pair of primes. All
four old-group permutability identities are arithmetic theorems. -/
theorem localNew_projections_commute (N : ℕ) (hN : 0<N) (p q : ℕ) :
    Commute (AsymptoticTotalNewCorner.localSpace N hN p).starProjection
      (AsymptoticTotalNewCorner.localSpace N hN q).starProjection := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hpq : p=q
  · subst q
    exact Commute.refl _
  by_cases hp : p.Prime ∧ p∣N
  · by_cases hq : q.Prime ∧ q∣N
    · have hep : AsymptoticTotalNewCorner.localSpace N hN p=
          AsymptoticQuotientOperators.newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))
            (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2)) := by
        simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left hp]
      have heq : AsymptoticTotalNewCorner.localSpace N hN q=
          AsymptoticQuotientOperators.newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hq.2))
            (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hq.2)) := by
        simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left hq]
      rw [starProjection_congr _ _ hep,starProjection_congr _ _ heq]
      exact new_projections_commute_of_permutable _ _ _ _
        (QuantitativeArithmeticCrossPrime.first_first_permute N p q hN hp.1 hq.1 hp.2 hq.2 hpq)
        (QuantitativeArithmeticCrossPrime.first_second_permute N p q hN hp.1 hq.1 hp.2 hq.2 hpq)
        (QuantitativeArithmeticCrossPrime.second_first_permute N p q hN hp.1 hq.1 hp.2 hq.2 hpq)
        (QuantitativeArithmeticCrossPrime.second_second_permute N p q hN hp.1 hq.1 hp.2 hq.2 hpq)
    · have heq : AsymptoticTotalNewCorner.localSpace N hN q=⊤ := by
        simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hq]
      rw [starProjection_congr _ _ heq,Submodule.starProjection_top]
      exact Commute.one_right _
  · have hep : AsymptoticTotalNewCorner.localSpace N hN p=⊤ := by
      simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hp]
    rw [starProjection_congr _ _ hep,Submodule.starProjection_top]
    exact Commute.one_left _

/-- Positive global old gap for the literal joint new quotient space.
No local, joint, commutation, or arithmetic gap premise is supplied. -/
theorem totalNew_old_energy_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ, 0<γ ∧ ∀ f : ℓ²(Classes (gamma N),ℂ),
      γ*‖f-(AsymptoticTotalNewCorner.space N hN).starProjection f‖^2≤
        (N.primeFactors.toList.map fun p => localOldEnergy N hN p f).sum := by
  obtain ⟨γ,hγ,hgap⟩ := finite_local_energy_gap N hN N.primeFactors.toList
  refine ⟨γ,hγ,?_⟩
  intro f
  rw [starProjection_congr _ _ (totalNewSpace_eq_jointList N hN)]
  exact (mul_le_mul_of_nonneg_left
    (jointListSpace_distance _ (localNew_projections_commute N hN) _ f) hγ.le).trans (hgap f)

/-- Uniform actual weighted all-prime gap. The positive coefficient is
chosen before every weight, exponent, root, and quotient vector. -/
theorem totalNew_weighted_old_energy_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ, 0<γ ∧ ∀ {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
      (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
      v∈AsymptoticCongruenceQuotient.quotientSpace N hε ht z →
      γ*‖v-(AsymptoticTotalNewCorner.stripSpace N hN hε ht z).starProjection v‖^2≤
        (N.primeFactors.toList.map fun p => weightedLocalOldEnergy N hN p hε ht z v).sum := by
  obtain ⟨γ,hγ,hgap⟩ := totalNew_old_energy_gap N hN
  refine ⟨γ,hγ,?_⟩
  intro ε hε t ht z v hv
  obtain ⟨f,rfl⟩ := hv
  simp only [LinearIsometry.coe_toLinearMap,totalNew_induction_distance,
    weightedLocalOldEnergy_induction]
  exact hgap f

#print axioms localNew_projections_commute
#print axioms totalNew_old_energy_gap
#print axioms totalNew_weighted_old_energy_gap

end QuantitativeNewGap
