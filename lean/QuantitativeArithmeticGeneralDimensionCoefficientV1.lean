module

public import QuantitativeArithmeticGeneralDimensionV1
public import QuantitativeArithmeticGeneralNewCoefficientV1
public import AsymptoticClassicalNewDimensionArithmeticV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticGeneralDimension

open UpperHalfPlane Filter AsymptoticSectorComparison AsymptoticClassicalCusp
open AsymptoticClassicalDimension AsymptoticCongruenceStrip
open QuantitativeArithmeticGeneralNewCoefficient

theorem fullLeading_mul_ramified (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hd : p∣M) :
    fullLeading (p*M)=(p:ℝ)*fullLeading M := by
  have he := Subgroup.relIndex_mul_relIndex (gamma (p*M)) (gamma M) (gamma 1)
    (gamma_le_of_dvd (Nat.dvd_mul_left M p)) (gamma_le_of_dvd (one_dvd M))
  rw [AsymptoticRamifiedCosets.projective_index M p hM hp.pos hd] at he
  unfold fullLeading
  rw [← he,Nat.cast_mul]
  ring

theorem factor_mul_other (M p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : q≠p) :
    localFactor (p*M) q=localFactor M q := by
  have hc : q.Coprime p := hq.coprime_iff_not_dvd.mpr (by
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))
  simp only [localFactor,(hc.pow_left 2).dvd_mul_left,(hc.pow_left 3).dvd_mul_left]

theorem simple_leading_factor (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hd : ¬p∣M) :
    fullLeading (p*M)-2*fullLeading M=fullLeading (p*M)*localFactor (p*M) p := by
  have hs : ¬p^2∣p*M := by simpa only [pow_two,Nat.mul_dvd_mul_iff_left hp.pos] using hd
  rw [localFactor,ite_eq_right hs,fullLeading_mul_prime M p hM hp hd]
  have hz : (p:ℝ)+1≠0 := by positivity
  field_simp
  ring

theorem repeated_leading_factor (L p : ℕ) (hL : 0<L) (hp : p.Prime) :
    fullLeading (p*(p*L))-2*fullLeading (p*L)+fullLeading L=
      fullLeading (p*(p*L))*localFactor (p*(p*L)) p := by
  have h2 : p^2∣p*(p*L) := ⟨L,by ring⟩
  have h3 : p^3∣p*(p*L) ↔ p∣L := by
    rw [show p*(p*L)=p^2*L by ring,show p^3=p^2*p by ring]
    exact Nat.mul_dvd_mul_iff_left (pow_pos hp.pos 2)
  have hz : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  have hz1 : (p:ℝ)+1≠0 := by positivity
  rw [localFactor,ite_eq_left h2,
    fullLeading_mul_ramified (p*L) p (Nat.mul_pos hp.pos hL) hp (Nat.dvd_mul_right p L)]
  by_cases hd : p∣L
  · rw [ite_eq_left (h3.mpr hd),fullLeading_mul_ramified L p hL hp hd]
    field_simp
  · rw [ite_eq_right (fun h => hd (h3.mp h)),fullLeading_mul_prime L p hL hp hd]
    field_simp

theorem leading_product (ps : List ℕ) (hd : ps.Nodup)
    (hp : ∀p∈ps,p.Prime) (N : ℕ) (hN : 0<N) (hdiv : ∀p∈ps,p∣N) :
    leading ps N=fullLeading N*(ps.map (localFactor N)).prod := by
  induction ps generalizing N with
  | nil => simp [leading]
  | cons p ps ih =>
    have hprime := hp p List.mem_cons_self
    have hdt := (List.nodup_cons.mp hd).2
    have hpt : ∀q∈ps,q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hne : ∀q∈ps,q≠p := by
      intro q hq he
      exact (List.nodup_cons.mp hd).1 (he ▸ hq)
    obtain ⟨M,rfl⟩ := hdiv p List.mem_cons_self
    have hM : 0<M := by
      by_contra hz
      have : M=0 := by omega
      simp [this] at hN
    have hdivu : ∀q∈ps,q∣p*M := fun q hq => hdiv q (List.mem_cons_of_mem p hq)
    have hdivm : ∀q∈ps,q∣M := by
      intro q hq
      exact ((hpt q hq).dvd_mul.mp (hdivu q hq)).resolve_left
        (fun h => hne q hq ((Nat.prime_dvd_prime_iff_eq (hpt q hq) hprime).mp h))
    have hprod (L : ℕ) : (ps.map (localFactor (p*L))).prod=(ps.map (localFactor L)).prod := by
      congr 1
      apply List.map_congr_left
      intro q hq
      exact factor_mul_other L p q hprime (hpt q hq) (hne q hq)
    have hdM : p*M/p=M := Nat.mul_div_cancel_left M hprime.pos
    simp only [leading,ite_eq_left (Nat.dvd_mul_right p M),hdM,List.map_cons,List.prod_cons]
    rw [ih hdt hpt (p*M) hN hdivu,ih hdt hpt M hM hdivm,hprod M]
    by_cases hr : p∣M
    · obtain ⟨L,rfl⟩ := hr
      have hL : 0<L := by
        by_contra hz
        have : L=0 := by omega
        simp [this] at hM
      have hdivl : ∀q∈ps,q∣L := by
        intro q hq
        exact ((hpt q hq).dvd_mul.mp (hdivm q hq)).resolve_left
          (fun h => hne q hq ((Nat.prime_dvd_prime_iff_eq (hpt q hq) hprime).mp h))
      rw [ite_eq_left (Nat.dvd_mul_right p L),Nat.mul_div_cancel_left L hprime.pos,
        ih hdt hpt L hL hdivl,hprod L]
      have he := repeated_leading_factor L p hL hprime
      linear_combination (ps.map (localFactor L)).prod*he
    · rw [ite_eq_right hr]
      have he := simple_leading_factor M p hM hprime hr
      linear_combination (ps.map (localFactor M)).prod*he

theorem leading_eq_coefficient (N : ℕ) (hN : 0<N) :
    leading N.primeFactors.toList N=AsymptoticTotalNewCorner.coefficient N hN := by
  rw [QuantitativeArithmeticGeneralNewCoefficient.coefficient_eq_arithmetic N hN]
  rw [leading_product N.primeFactors.toList N.primeFactors.nodup_toList
    (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_toList.mp hp)).1) N hN
    (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_toList.mp hp)).2.1)]
  rw [Finset.prod_map_toList]
  rfl

/-- General-level classical newspace dimensions have the exact actual
regular-incidence leading coefficient and a bounded remainder. -/
theorem new_dimension_coefficient_bounded (N : ℕ) (hN : 0<N) :
    ∃ B : ℝ,∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (newSpace N hN (k:ℤ)):ℝ)-
        AsymptoticTotalNewCorner.coefficient N hN*k|≤B := by
  simpa only [leading_eq_coefficient N hN] using new_dimension_bounded N hN

#print axioms leading_product
#print axioms leading_eq_coefficient
#print axioms new_dimension_coefficient_bounded

end QuantitativeArithmeticGeneralDimension
