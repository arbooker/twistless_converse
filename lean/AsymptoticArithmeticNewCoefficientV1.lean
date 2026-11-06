module

public import AsymptoticTotalNewTraceV1
public import AsymptoticPrimeNewRootV1
public import GridAdmissibleGapV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticTotalNewCorner

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticRegularTrace
open AsymptoticPolarIsometry AsymptoticQuotientOperators

/-- Normalized local new factor at an admissible level. The square and
higher branches can occur only at p=2. -/
noncomputable def localFactor (N p : ℕ) : ℝ :=
  if p^2∣N then if p^3∣N then 1/4 else 1/6 else ((p:ℝ)-1)/((p:ℝ)+1)

/-- An arithmetic form of the total coefficient: the congruence index
and explicit local rational factors, with no operator or sector data. -/
noncomputable def arithmeticCoefficient (N : ℕ) : ℝ :=
  ((gamma N).relIndex (gamma 1):ℝ)/12*∏ p∈N.primeFactors,localFactor N p

theorem localSpace_root_eq_factor (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (p : ℕ) (hp : p.Prime) (hpN : p∣N) :
    (matrix (localSpace N hN.1 p).starProjection (classOf (gamma N) 1) (classOf (gamma N) 1)).re=
      localFactor N p := by
  by_cases hs : p^2∣N
  · have hp2 : p=2 := by
      by_contra hn
      exact hN.2.2 p hp hn hs
    subst p
    obtain ⟨L,hNL⟩ := hs
    have he : N=2*(2*L) := by rw [hNL]; ring
    clear hNL
    subst N
    have hL : 0<L := by have hh := hN.1; nlinarith
    let : NeZero (2*(2*L)) := ⟨hN.1.ne'⟩
    rw [starProjection_congr _ _ (localSpace_mul_eq (2*L) 2 (by omega) Nat.prime_two)]
    have h4 : 2^2∣2*(2*L) := ⟨L,by ring⟩
    have h8 : 2^3∣2*(2*L) ↔ 2∣L := by
      rw [show 2*(2*L)=4*L by ring,show 2^3=4*2 by decide]
      exact Nat.mul_dvd_mul_iff_left (by decide : 0<4)
    unfold localFactor
    rw [ite_eq_left h4]
    by_cases hL2 : 2∣L
    · rw [ite_eq_left (h8.mpr hL2)]
      exact higher_two_new_root L hL hL2
    · rw [ite_eq_right (fun h => hL2 (h8.mp h))]
      exact square_two_new_root L hL hL2
  · obtain ⟨M,rfl⟩ := hpN
    have hM : 0<M := by have hh := hN.1; nlinarith
    let : NeZero (p*M) := ⟨hN.1.ne'⟩
    let : Fact p.Prime := ⟨hp⟩
    have hpM : ¬p∣M := by
      intro hm
      apply hs
      rw [pow_two]
      exact Nat.mul_dvd_mul_left p hm
    rw [starProjection_congr _ _ (localSpace_mul_eq M p hM hp)]
    change (matrix _ _ _).re=localFactor (p*M) p
    rw [localFactor,ite_eq_right hs]
    exact simple_new_root M p hM hpM

theorem coefficient_eq_arithmetic (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    coefficient N hN.1=arithmeticCoefficient N := by
  unfold coefficient arithmeticCoefficient
  rw [Finset.prod_map_toList]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  exact localSpace_root_eq_factor N hN p hpp hpd

/-- The sharp summed analytic bound now has a purely arithmetic
coefficient for every admissible level. -/
theorem totalTrace_le_arithmetic (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    AsymptoticQuotientIncidence.totalTrace N hN.1 hε ht≤4*Real.pi*arithmeticCoefficient N := by
  rw [← coefficient_eq_arithmetic N hN]
  exact totalTrace_le_coefficient N hN.1 hε ht

#print axioms localSpace_root_eq_factor
#print axioms coefficient_eq_arithmetic
#print axioms totalTrace_le_arithmetic

end AsymptoticTotalNewCorner
