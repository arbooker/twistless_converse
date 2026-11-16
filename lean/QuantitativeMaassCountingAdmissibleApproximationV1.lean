module

public import QuantitativeMaassCountingSimpleApproximationV1
public import QuantitativeMaassCountingRepeatedProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open QuantitativeNewGap ContinuousLinearMap AsymptoticPolarIsometry
open QuantitativeArithmeticNewBandProjections
namespace QuantitativeMaass.Counting

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

theorem divisorSimpleNewFilter_approximation {M N : ℕ} [NeZero M] [NeZero N]
    (hN : 0<N) (hMN : M∣N) (p : ℕ) [Fact p.Prime]
    (hpMN : p*M=N) (hpM : ¬p∣M) :
    ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∀ m : ℕ,
      ‖simpleNewFilter hN hMN p m-
        (newSpace (gamma_le_of_dvd hMN) (gamma_le_frickeOldGroup hN hMN)).starProjection‖≤ρ^m := by
  subst N
  exact simpleNewFilter_operator_approximation M p (NeZero.pos M) hpM

theorem divisorRepeatedTwoNewFilter_exact {M N : ℕ} [NeZero M] [NeZero N]
    (hN : 0<N) (hMN : M∣N) (hNM : 2*M=N) (hM2 : 2∣M) :
    repeatedTwoNewFilter hN hMN=
      (newSpace (gamma_le_of_dvd hMN) (gamma_le_frickeOldGroup hN hMN)).starProjection := by
  obtain ⟨L,rfl⟩ := hM2
  subst N
  have hL : 0<L := by have hm := NeZero.pos (2*L); omega
  exact repeatedTwoNewFilter_newSpace L hL

/-- Every actual local counting filter converges geometrically to the
corresponding local-new projection at an admissible level. -/
theorem localNewFilter_approximation (N : ℕ) [NeZero N] (hN : 0<N)
    (hAd : GridAdmissibleGap.Admissible N) (p : ↥N.primeFactors) :
    ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∀ m : ℕ,
      ‖localNewFilter N hN m p-(AsymptoticTotalNewCorner.localSpace N hN p.val).starProjection‖≤ρ^m := by
  classical
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hpN := Nat.dvd_of_mem_primeFactors p.property
  let : Fact p.val.Prime := ⟨hp⟩
  have hspace : AsymptoticTotalNewCorner.localSpace N hN p.val=
      newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hpN))
        (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hpN)) := by
    simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left (show p.val.Prime ∧ p.val∣N from ⟨hp,hpN⟩)]
  simp_rw [starProjection_congr _ _ hspace]
  by_cases h : p.val∣N/p.val
  · have hp2 := (admissible_prime_filter_cases N p.val hAd hp hpN).resolve_left (not_not.mpr h)
    have he : 2*(N/p.val)=N := by rw [←hp2.1]; exact Nat.mul_div_cancel' hpN
    have hd : 2∣N/p.val := by simpa only [hp2.1] using h
    refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro m
    rw [localNewFilter,ite_eq_left h,divisorRepeatedTwoNewFilter_exact hN _ he hd,sub_self,norm_zero]
    positivity
  · simpa only [localNewFilter,ite_eq_right h] using
      divisorSimpleNewFilter_approximation hN (Nat.div_dvd_of_dvd hpN) p.val
        (Nat.mul_div_cancel' hpN) h

#print axioms divisorSimpleNewFilter_approximation
#print axioms divisorRepeatedTwoNewFilter_exact
#print axioms localNewFilter_approximation
end QuantitativeMaass.Counting
