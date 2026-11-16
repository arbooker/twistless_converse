module

public import QuantitativeMaassCompletedLocalAtkinV1
public import QuantitativeMaassNormalizerTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticClassicalPetersson
open QuantitativeNewGap QuantitativeArithmeticAtkinSigns QuantitativeArithmeticCrossPrime
open QuantitativeNinaMaass
namespace QuantitativeMaass

/-- At a different prime, the same local Atkin matrix normalizes the
literal lower-level congruence group. -/
def completedLocalAtkinLowerOther (N : ℕ) (hN : 0<N) (p : SimplePrime N)
    (q : ℕ) (hq : q.Prime) (hqN : q∣N) (hpq : p.val≠q) : quotientNormalizerGroup (N/q) :=
  ⟨localAtkinLabel N hN p,by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hh := other_old_iff_level N p.val q hN (simplePrime_prime p) hq
      (simplePrime_dvd p) hqN hpq (simplePrime_colevel_pos N hN p)
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) false a
    simpa only [oldGroup,Bool.false_eq_true,ite_false,localAtkinLabel] using hh⟩

/-- At its own prime, Fricke followed by the local Atkin action normalizes
the lower-level group, by the actual old-direction swap. -/
def completedLocalAtkinLowerOwn (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    quotientNormalizerGroup (N/p.val) :=
  ⟨((completedFrickeNormalizer N hN)⁻¹*completedLocalAtkinNormalizer N hN p).val,by
    let W := (completedFrickeNormalizer N hN).val
    let g := (completedLocalAtkinNormalizer N hN p).val
    change W⁻¹*g∈quotientNormalizerGroup (N/p.val)
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hs : a∈gamma (N/p.val) ↔ g*a*g⁻¹∈frickeOldGroup N (N/p.val) hN := by
      have hh := own_old_iff_level N p.val hN (simplePrime_prime p) (simplePrime_dvd p)
        (simplePrime_colevel_pos N hN p) (Nat.gcdA p.val (N/p.val))
        (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p) false a
      simpa only [oldGroup,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,
        g,completedLocalAtkinNormalizer,localAtkinLabel] using hh
    constructor
    · intro ha
      obtain ⟨b,hb,hbe⟩ := hs.mp ha
      change W*b*W⁻¹=g*a*g⁻¹ at hbe
      have he : (W⁻¹*g)*a*(W⁻¹*g)⁻¹=b := by
        calc
          _ = W⁻¹*(g*a*g⁻¹)*W := by group
          _ = W⁻¹*(W*b*W⁻¹)*W := by rw [hbe]
          _ = b := by group
      rwa [he]
    · intro ha
      apply hs.mpr
      refine ⟨(W⁻¹*g)*a*(W⁻¹*g)⁻¹,ha,?_⟩
      change W*((W⁻¹*g)*a*(W⁻¹*g)⁻¹)*W⁻¹=g*a*g⁻¹
      group⟩

/-- The genuine trace at every other prime intertwines the local Atkin operator. -/
theorem completedLocalAtkin_other_trace (N : ℕ) [NeZero N] (hN : 0<N) (p : SimplePrime N)
    (q : ℕ) (hq : q.Prime) (hqN : q∣N) (hpq : p.val≠q) (x : AutomorphicSpace N) :
    levelTrace (Nat.div_dvd_of_dvd hqN)
      (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x)=
      quotientNormalizerPullback (N/q) (completedLocalAtkinLowerOther N hN p q hq hqN hpq)
        (levelTrace (Nat.div_dvd_of_dvd hqN) x) :=
  normalizer_levelTrace (Nat.div_dvd_of_dvd hqN) _ _ rfl x

/-- At the local prime the two actual trace equations are interchanged,
up to an invertible lower-level normalizer. -/
theorem completedLocalAtkin_own_trace (N : ℕ) [NeZero N] (hN : 0<N) (p : SimplePrime N)
    (x : AutomorphicSpace N) :
    levelTrace (Nat.div_dvd_of_dvd (simplePrime_dvd p))
      (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x)=
      quotientNormalizerPullback (N/p.val) (completedLocalAtkinLowerOwn N hN p)
        (levelTrace (Nat.div_dvd_of_dvd (simplePrime_dvd p)) (frickeIsometry N hN x)) := by
  let W := completedFrickeNormalizer N hN
  let g := completedLocalAtkinNormalizer N hN p
  have hh := normalizer_levelTrace (Nat.div_dvd_of_dvd (simplePrime_dvd p)) (W⁻¹*g)
    (completedLocalAtkinLowerOwn N hN p) rfl (quotientNormalizerPullback N W x)
  rw [←quotientNormalizerPullback_mul,show W*(W⁻¹*g)=g by group] at hh
  exact hh

#print axioms completedLocalAtkinLowerOther
#print axioms completedLocalAtkinLowerOwn
#print axioms completedLocalAtkin_other_trace
#print axioms completedLocalAtkin_own_trace
end QuantitativeMaass
