module

public import QuantitativeMaassTwoProjectionOperatorGapV1
public import QuantitativeNewGapRepeatedAllV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.Counting

/-- On the actual infinite counting quotient, every prime divisor has a
geometrically convergent averaged-old-projection polynomial. This covers
both simple primes and arbitrary repeated ramification. -/
theorem prime_old_operator_approximation (M p : ℕ) (hM : 0<M) (hp : p.Prime) :
    let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    let hN := Nat.mul_pos hp.pos hM
    let P := (space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection
    let Q := (space (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))).starProjection
    let U := newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))
    ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∀ m : ℕ,
      ‖(1-(1/2:ℂ) • (P+Q))^m-U.starProjection‖ ≤ ρ^m := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  intro _ hN P Q U
  obtain ⟨γ,hγ,hgap⟩ := prime_coset_old_gap M p hM hp
  let c := min γ 1
  have hc : 0<c := lt_min hγ zero_lt_one
  have hc1 : c≤1 := min_le_right _ _
  have hcγ : c≤γ := min_le_left _ _
  have hs : Real.sqrt (1-c/2)<1 := by
    have he := Real.sq_sqrt (by linarith : 0≤1-c/2)
    have hn := Real.sqrt_nonneg (1-c/2)
    nlinarith
  refine ⟨Real.sqrt (1-c/2),Real.sqrt_nonneg _,hs,?_⟩
  intro m
  apply two_projection_operator_approximation P Q
    (Submodule.starProjection_isSymmetric _) (Submodule.starProjection_isSymmetric _)
    (Submodule.isIdempotentElem_starProjection _) (Submodule.isIdempotentElem_starProjection _)
    U (fun w hw => (newSpace_mem _ _ w).mp hw) c (by linarith) _ m
  intro w
  exact (mul_le_mul_of_nonneg_right hcγ (sq_nonneg _)).trans (hgap w)

#print axioms prime_old_operator_approximation
end QuantitativeMaass.Counting
