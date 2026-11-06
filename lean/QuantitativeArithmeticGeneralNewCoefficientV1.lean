module

public import QuantitativeArithmeticRepeatedJoinV1
public import AsymptoticPrimeNewRootV1
public import AsymptoticTotalNewTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticGeneralNewCoefficient

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticRamifiedCosets AsymptoticCongruenceOldSpace
open AsymptoticCongruenceQuotient AsymptoticNestedQuotients
open AsymptoticPolarIsometry AsymptoticQuotientOperators
open scoped ENNReal

theorem repeated_new_trace (L p : ℕ) [Fact p.Prime] (hL : 0<L)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) :
    letI : NeZero (p*(p*L)) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos
      (Nat.mul_pos (Fact.out : p.Prime).pos hL)).ne'⟩
    (trace volume (fun z => (newSpace (p*(p*L)) (gamma (p*L))
      (frickeOldGroup (p*(p*L)) (p*L) (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hL)))
      (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
      (gamma_le_frickeOldGroup (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hL)) (Nat.dvd_mul_left (p*L) p)) hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection (p*(p*L)) hε ht)).toReal*
        (1-(p:ℝ)⁻¹*2+((p*(gamma (p*L)).relIndex (gamma L):ℕ):ℝ)⁻¹) := by
  have hp := (Fact.out : p.Prime).pos
  have hr : 0<(gamma (p*L)).relIndex (gamma L) := by
    by_cases hdiv : p∣L
    · rw [projective_index L p hL hp hdiv]
      exact hp
    · rw [projective_index_coprime L p hL (Fact.out : p.Prime)
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hdiv)]
      omega
  have hM := Nat.mul_pos hp hL
  have hN := Nat.mul_pos hp hM
  let : NeZero (p*(p*L)) := ⟨hN.ne'⟩
  let J := gamma (p*L)
  let K := frickeOldGroup (p*(p*L)) (p*L) hN
  have hi : (gamma (p*(p*L))).relIndex J=p := projective_index (p*L) p hM hp (Nat.dvd_mul_right p L)
  have hk : (gamma (p*(p*L))).relIndex K=p := by
    dsimp only [K]
    rw [frickeOldGroup_index]
    exact hi
  have hj : (gamma (p*(p*L))).relIndex (J⊔K)=p*(gamma (p*L)).relIndex (gamma L) := by
    dsimp only [J,K]
    rw [frickeOldGroup_eq_degeneracy (p*L) p hM hp]
    exact QuantitativeArithmeticRepeatedJoin.repeated_join_index L p hL
  let : Finite (↥(J⊔K) ⧸ (gamma (p*(p*L))).subgroupOf (J⊔K)) := by
    apply Subgroup.index_ne_zero_iff_finite.mp
    change (gamma (p*(p*L))).relIndex (J⊔K)≠0
    rw [hj]
    exact (Nat.mul_pos hp hr).ne'
  have he := new_trace_finite_join (p*(p*L)) J K
    (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
    (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left (p*L) p)) hε ht hN
  have hi' : ((gamma (p*(p*L))).subgroupOf J).index=p := hi
  have hk' : ((gamma (p*(p*L))).subgroupOf K).index=p := hk
  have hj' : ((gamma (p*(p*L))).subgroupOf (J⊔K)).index=p*(gamma (p*L)).relIndex (gamma L) := hj
  rw [hi',hk',hj'] at he
  convert he using 1
  ring

/-- The exact local root at every repeated prime. -/
theorem repeated_new_root (L p : ℕ) [Fact p.Prime] (hL : 0<L) :
    letI : NeZero (p*(p*L)) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos
      (Nat.mul_pos (Fact.out : p.Prime).pos hL)).ne'⟩
    (matrix (AsymptoticQuotientOperators.newSpace
      (gamma_le_of_dvd (Nat.dvd_mul_left (p*L) p))
      (gamma_le_frickeOldGroup (Nat.mul_pos (Fact.out : p.Prime).pos
        (Nat.mul_pos (Fact.out : p.Prime).pos hL))
        (Nat.dvd_mul_left (p*L) p))).starProjection
      (classOf (p*(p*L)) 1) (classOf (p*(p*L)) 1)).re=
        1-(p:ℝ)⁻¹*2+((p*(gamma (p*L)).relIndex (gamma L):ℕ):ℝ)⁻¹ := by
  have hN := Nat.mul_pos (Fact.out : p.Prime).pos (Nat.mul_pos (Fact.out : p.Prime).pos hL)
  let : NeZero (p*(p*L)) := ⟨hN.ne'⟩
  apply newSpace_root_of_trace (p*(p*L)) _ _ _ _ (ε:=1) (by norm_num) (t:=1) (by omega) hN
  exact repeated_new_trace L p hL (ε:=1) (by norm_num) (t:=1) (by omega)

/-- Local new factor without admissibility restrictions. -/
def localFactor (N p : ℕ) : ℝ :=
  if p^2∣N then
    if p^3∣N then 1-(p:ℝ)⁻¹*2+((p:ℝ)*p)⁻¹
    else 1-(p:ℝ)⁻¹*2+((p:ℝ)*(p+1))⁻¹
  else ((p:ℝ)-1)/((p:ℝ)+1)

def arithmeticCoefficient (N : ℕ) : ℝ :=
  ((gamma N).relIndex (gamma 1):ℝ)/12*∏ p∈N.primeFactors,localFactor N p

/-- The actual local-new projection has the classical factor at every
prime and every exponent. -/
theorem localSpace_root_eq_factor (N : ℕ) (hN : 0<N)
    (p : ℕ) (hp : p.Prime) (hpN : p∣N) :
    (matrix (AsymptoticTotalNewCorner.localSpace N hN p).starProjection
      (classOf (gamma N) 1) (classOf (gamma N) 1)).re=localFactor N p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hs : p^2∣N
  · obtain ⟨L,hNL⟩ := hs
    have he : N=p*(p*L) := by rw [hNL]; ring
    clear hNL
    subst N
    have hL : 0<L := by
      by_contra h
      have hz : L=0 := by omega
      simp [hz] at hN
    let : NeZero (p*(p*L)) := ⟨hN.ne'⟩
    rw [starProjection_congr _ _ (AsymptoticTotalNewCorner.localSpace_mul_eq (p*L) p
      (Nat.mul_pos hp.pos hL) hp)]
    have h2 : p^2∣p*(p*L) := ⟨L,by ring⟩
    have h3 : p^3∣p*(p*L) ↔ p∣L := by
      rw [show p*(p*L)=p^2*L by ring,show p^3=p^2*p by ring]
      exact Nat.mul_dvd_mul_iff_left (pow_pos hp.pos 2)
    apply (repeated_new_root L p hL).trans
    rw [localFactor,ite_eq_left h2]
    by_cases hd : p∣L
    · rw [ite_eq_left (h3.mpr hd),projective_index L p hL hp.pos hd]
      norm_cast
    · rw [ite_eq_right (fun h => hd (h3.mp h)),projective_index_coprime L p hL hp
        (hp.coprime_iff_not_dvd.mpr hd)]
      push_cast
      rfl
  · obtain ⟨M,rfl⟩ := hpN
    have hM : 0<M := by
      by_contra h
      have hz : M=0 := by omega
      simp [hz] at hN
    let : NeZero (p*M) := ⟨hN.ne'⟩
    have hpM : ¬p∣M := by
      intro hm
      apply hs
      rw [pow_two]
      exact Nat.mul_dvd_mul_left p hm
    rw [starProjection_congr _ _ (AsymptoticTotalNewCorner.localSpace_mul_eq M p hM hp)]
    rw [localFactor,ite_eq_right hs]
    exact simple_new_root M p hM hpM

/-- The total incidence coefficient is explicit at every positive level. -/
theorem coefficient_eq_arithmetic (N : ℕ) (hN : 0<N) :
    AsymptoticTotalNewCorner.coefficient N hN=arithmeticCoefficient N := by
  unfold AsymptoticTotalNewCorner.coefficient arithmeticCoefficient
  rw [Finset.prod_map_toList]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  exact localSpace_root_eq_factor N hN p hpp hpd

#print axioms repeated_new_trace
#print axioms repeated_new_root
#print axioms localSpace_root_eq_factor
#print axioms coefficient_eq_arithmetic

end QuantitativeArithmeticGeneralNewCoefficient
