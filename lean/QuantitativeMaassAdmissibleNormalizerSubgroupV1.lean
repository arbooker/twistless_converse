module
public import QuantitativeMaassDivisorSubgroupClosureV1
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open QuantitativeNewGap AsymptoticCongruenceStrip AsymptoticSectorSigns AsymptoticFreshMatrices
namespace QuantitativeMaass.CountingMetric
variable (N : ℕ) (hN : 0<N) (K : Subgroup AsymptoticRationalGroup.Group) (hK : gamma N≤K)
include hK
/-- At admissible levels every exact Atkin generator belongs to any
subgroup containing the congruence group, Fricke and simple Atkin generators.
This group statement applies equally to counting and physical actions. -/
theorem admissible_atkin_mem (hAd : GridAdmissibleGap.Admissible N)
    (hW : frickeLabel N hN∈K)
    (hS : ∀ p : SimplePrime N,(simpleAtkinGeneratorIndex N hN p).val∈K)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) : divisorMem N hN K Q := by
  apply admissible_exact_predicate N hAd (divisorMem N hN K) _ _
    (divisorMem_mul N hN K hK) (divisorMem_cancel N hN K hK) _ Q D hQD hcop
  · intro i hi
    obtain ⟨D,h1,A,B,hAB,hDN,hi⟩ := hi
    have hD : D=N := by simpa only [one_mul] using hDN
    subst D
    rw [hi]
    exact hK (exactAtkin_one_mem N A B hAB)
  · intro i hi
    obtain ⟨D,hN',A,B,hAB,hND,hi⟩ := hi
    have hD : D=1 := Nat.eq_of_mul_eq_mul_left hN (hND.trans (mul_one N).symm)
    subst D
    obtain ⟨a,ha⟩ := exactAtkin_full_fricke N hN A B hAB
    rw [hi,ha]
    exact K.mul_mem (hK a.property) hW
  · intro p hp i hi
    exact (generator_mem_congr N hN K hK p (simpleAtkinGeneratorIndex N hN ⟨p,hp⟩) i
      ⟨N/p,(simplePrime_prime ⟨p,hp⟩).pos,_,_,simplePrime_bezout N ⟨p,hp⟩,
        Nat.mul_div_cancel' (simplePrime_dvd ⟨p,hp⟩),rfl⟩ hi).mp (hS ⟨p,hp⟩)

#print axioms generator_mem_congr
#print axioms divisorMem_mul
#print axioms divisorMem_cancel
#print axioms admissible_atkin_mem
end QuantitativeMaass.CountingMetric
