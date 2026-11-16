module

public import QuantitativeMaassGeneratorInvolutionsV1
public import QuantitativeMaassDyadicTraceOperatorV1
public import QuantitativeNewGapLocalAtkinV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNewGap
open QuantitativeArithmeticAtkinSigns
namespace QuantitativeMaass

/-- A congruence-valued commutator gives commuting actual Hilbert-space
operators, not merely commuting permutations of rational cosets. -/
theorem quotientNormalizerPullback_commute (N : ℕ) (g h : quotientNormalizerGroup N)
    (hc : g.val*h.val*g.val⁻¹*h.val⁻¹∈gamma N) :
    Commute (quotientNormalizerPullback N g).toContinuousLinearMap
      (quotientNormalizerPullback N h).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change quotientNormalizerPullback N g (quotientNormalizerPullback N h x)=
    quotientNormalizerPullback N h (quotientNormalizerPullback N g x)
  rw [←quotientNormalizerPullback_mul,←quotientNormalizerPullback_mul]
  symm
  apply quotientNormalizerPullback_left_gamma N (g*h) (h*g)
    ⟨g.val*h.val*g.val⁻¹*h.val⁻¹,hc⟩
  change g.val*h.val=(g.val*h.val*g.val⁻¹*h.val⁻¹)*(h.val*g.val)
  group

/-- The canonical simple-prime Atkin normalizer on the actual quotient. -/
def completedLocalAtkinNormalizer (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    quotientNormalizerGroup N :=
  ⟨localAtkinLabel N hN p,normalizer_mem_of_conjugations N _
    (localAtkinLabel_conj N hN p) (localAtkinLabel_inv_conj N hN p)⟩

theorem completedLocalAtkin_involutive (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Function.Involutive (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)) := by
  intro x
  rw [←quotientNormalizerPullback_mul]
  exact quotientNormalizerPullback_gamma N _ (localAtkinLabel_square N hN p) x

theorem completedLocalAtkin_selfAdjoint (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    IsSelfAdjoint (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap := by
  exact AutomorphicL2.normalizerIsometry_selfAdjoint MeasureTheory.volume
    AsymptoticRationalGroup.measurePreserving (gamma N) (localAtkinLabel N hN p)
    (localAtkinLabel_conj N hN p) (localAtkinLabel_inv_conj N hN p)
    (density N) (density_measurable N) (density_orbit_sum N) (localAtkinLabel_square N hN p)

theorem completedLocalAtkin_fricke_commute (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Commute (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap
      (quotientNormalizerPullback N (completedFrickeNormalizer N hN)).toContinuousLinearMap := by
  apply quotientNormalizerPullback_commute
  exact localAtkin_fricke_commutator_mem_level N p.val hN (simplePrime_prime p)
    (simplePrime_dvd p) (simplePrime_colevel_pos N hN p)
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)

theorem completedLocalAtkin_pair_commute (N : ℕ) (hN : 0<N) (p q : SimplePrime N) :
    Commute (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap
      (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN q)).toContinuousLinearMap := by
  by_cases hpq : p=q
  · subst q
    exact Commute.refl _
  apply quotientNormalizerPullback_commute
  exact localAtkin_pair_commutator_mem_level N p.val q.val hN
    (simplePrime_prime p) (simplePrime_prime q) (simplePrime_dvd p) (simplePrime_dvd q)
    (fun hh => hpq (Subtype.ext hh)) (simplePrime_colevel_pos N hN p) (simplePrime_colevel_pos N hN q)
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val))
    (Nat.gcdA q.val (N/q.val)) (Nat.gcdB q.val (N/q.val))
    (simplePrime_bezout N p) (simplePrime_bezout N q)

#print axioms quotientNormalizerPullback_commute
#print axioms completedLocalAtkin_involutive
#print axioms completedLocalAtkin_selfAdjoint
#print axioms completedLocalAtkin_fricke_commute
#print axioms completedLocalAtkin_pair_commute
end QuantitativeMaass
