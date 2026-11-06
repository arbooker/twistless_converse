module

public import QuantitativeNewGapLocalAtkinV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticQuotientOperators
open AsymptoticPermutationInvariant AsymptoticPolarIsometry QuantitativeArithmeticAtkinSigns
open QuantitativeArithmeticCrossPrime

theorem localAtkin_localNew_invariant (N : ℕ) (hN : 0<N) (p : SimplePrime N) (q : ℕ) :
    Invariant (localAtkinEquiv N hN p) (AsymptoticTotalNewCorner.localSpace N hN q).starProjection := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hq : q.Prime ∧ q∣N
  · have he : AsymptoticTotalNewCorner.localSpace N hN q=
        newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hq.2))
          (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hq.2)) := by
      simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left hq]
    rw [starProjection_congr _ _ he]
    by_cases hpq : p.val=q
    · subst q
      apply normalizer_new_invariant_swap
      · exact localAtkinLabel_square N hN p
      · intro g
        have hh := own_old_iff_level N p.val hN (simplePrime_prime p) (simplePrime_dvd p)
          (simplePrime_colevel_pos N hN p) (Nat.gcdA p.val (N/p.val))
          (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) true g
        simpa only [oldGroup,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,localAtkinLabel] using hh.symm
      · exact (frickeOldGroup_index N (N/p.val) hN).symm
    · apply normalizer_new_invariant_fixed
      · intro g
        have hh := other_old_iff_level N p.val q hN (simplePrime_prime p) hq.1
          (simplePrime_dvd p) hq.2 hpq (simplePrime_colevel_pos N hN p)
          (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) false g
        simpa only [oldGroup,Bool.false_eq_true,ite_false,localAtkinLabel] using hh.symm
      · intro g
        have hh := other_old_iff_level N p.val q hN (simplePrime_prime p) hq.1
          (simplePrime_dvd p) hq.2 hpq (simplePrime_colevel_pos N hN p)
          (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) true g
        simpa only [oldGroup,ite_true,localAtkinLabel] using hh.symm
  · have he : AsymptoticTotalNewCorner.localSpace N hN q=⊤ := by
      simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hq]
    rw [starProjection_congr _ _ he,Submodule.starProjection_top]
    exact invariant_one _

/-- Every canonical local Atkin involution preserves the literal
all-prime new projector, including every repeated-prime constraint. -/
theorem localAtkin_totalNew_invariant (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Invariant (localAtkinEquiv N hN p) (AsymptoticTotalNewCorner.space N hN).starProjection := by
  rw [starProjection_congr _ _ (totalNewSpace_eq_jointList N hN)]
  exact invariant_jointListSpace _ _ (localAtkin_localNew_invariant N hN p) _

theorem localAtkin_totalNew_sign_commute (N : ℕ) (hN : 0<N) (p : SimplePrime N) (s : ℝ) :
    Commute (AsymptoticTotalNewCorner.space N hN).starProjection
      (permutationSignSpace (localAtkinEquiv N hN p) s).starProjection :=
  invariant_commute_signProjection _ (localAtkinEquiv_involutive N hN p) _
    (localAtkin_totalNew_invariant N hN p) s

#print axioms localAtkin_localNew_invariant
#print axioms localAtkin_totalNew_invariant
#print axioms localAtkin_totalNew_sign_commute

end QuantitativeNewGap
