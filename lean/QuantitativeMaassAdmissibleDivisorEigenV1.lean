module

public import QuantitativeMaassDivisorUnitEigenV1
public import QuantitativeMaassExactDivisorPredicateV1
public import QuantitativeMaassPhysicalSectorProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticSectorSigns QuantitativeNewGap
namespace QuantitativeMaass

theorem divisorUnitEigen_one (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N) :
    divisorUnitEigen N hN x 1 := by
  intro i hi
  obtain ⟨D,h1,A,B,hAB,hDN,hi⟩ := hi
  have hD : D=N := by simpa only [one_mul] using hDN
  subst D
  have hg : (admissibleGeneratorLift N hN i).val∈gamma N := by
    change i.val∈gamma N
    rw [hi]
    exact exactAtkin_one_mem N A B hAB
  refine ⟨1,by norm_num,?_⟩
  rw [quotientNormalizerPullback_gamma N _ hg,one_smul]

theorem divisorUnitEigen_full (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N)
    (hW : completedFrickeNormalizer N hN∈normalizerEigenStabilizer N x) :
    divisorUnitEigen N hN x N := by
  intro i hi
  obtain ⟨D,hN',A,B,hAB,hND,hi⟩ := hi
  have hD : D=1 := Nat.eq_of_mul_eq_mul_left hN (hND.trans (mul_one N).symm)
  subst D
  obtain ⟨a,ha⟩ := exactAtkin_full_fricke N hN A B hAB
  have he := quotientNormalizerPullback_left_gamma N (admissibleGeneratorLift N hN i)
    (completedFrickeNormalizer N hN) a (by change i.val=a.val*_; rw [hi]; exact ha) x
  obtain ⟨c,hc,hcx⟩ := hW
  exact ⟨c,hc,he.trans hcx⟩

theorem divisorUnitEigen_simple (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N) (p : SimplePrime N)
    (hp : completedLocalAtkinNormalizer N hN p∈normalizerEigenStabilizer N x) :
    divisorUnitEigen N hN x p.val := by
  have he : admissibleGeneratorLift N hN (simpleAtkinGeneratorIndex N hN p)=
      completedLocalAtkinNormalizer N hN p := Subtype.ext (simpleAtkinGeneratorIndex_value N hN p)
  have hj : admissibleGeneratorLift N hN (simpleAtkinGeneratorIndex N hN p)∈normalizerEigenStabilizer N x := by
    rw [he]
    exact hp
  intro i hi
  exact (generator_unitEigen_congr N hN x p.val (simpleAtkinGeneratorIndex N hN p) i
    ⟨N/p.val,(simplePrime_prime p).pos,_,_,simplePrime_bezout N p,
      Nat.mul_div_cancel' (simplePrime_dvd p),rfl⟩ hi).mp hj

/-- The actual normalizer product and cancellation identities discharge
all exact-divisor unit-eigenvalue conditions from the finite original data. -/
theorem admissible_divisorUnitEigen (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (x : AutomorphicSpace N)
    (hW : completedFrickeNormalizer N hN.1∈normalizerEigenStabilizer N x)
    (hS : ∀ p : SimplePrime N,completedLocalAtkinNormalizer N hN.1 p∈normalizerEigenStabilizer N x)
    (Q D : ℕ) (hQD : Q*D=N) (hcop : Nat.Coprime Q D) :
    divisorUnitEigen N hN.1 x Q := by
  apply admissible_exact_predicate N hN (divisorUnitEigen N hN.1 x)
    (divisorUnitEigen_one N hN.1 x) (divisorUnitEigen_full N hN.1 x hW)
    (divisorUnitEigen_mul N hN.1 x) (divisorUnitEigen_cancel N hN.1 x) _ Q D hQD hcop
  intro p hp
  exact divisorUnitEigen_simple N hN.1 x ⟨p,hp⟩ (hS ⟨p,hp⟩)

#print axioms divisorUnitEigen_one
#print axioms divisorUnitEigen_full
#print axioms divisorUnitEigen_simple
#print axioms admissible_divisorUnitEigen
end QuantitativeMaass
