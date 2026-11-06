module

public import AsymptoticSimpleOldAnnihilationV1
public import AsymptoticFrickeCosetTransportV1
public import AsymptoticRepeatedNewCornerV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticSectorSigns AsymptoticRegularTrace
open scoped lp

theorem incidence_fricke_projection_zero_of_lower (N d : ℕ) (hN : 0<N) (hd : d∣N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector N) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : v∈AsymptoticQuotientIncidence.space N hN hε ht e x) :
    letI : NeZero N := ⟨hN.ne'⟩
    (lowerSpace hd hε ht x).starProjection v=0 →
      (frickeSpace hN hd hε ht x).starProjection v=0 := by
  let : NeZero N := ⟨hN.ne'⟩
  have hq := ((AsymptoticQuotientIncidence.space_mem N hN hε ht e x v).mp hv).1
  obtain ⟨f,rfl⟩ := hq
  change AsymptoticCongruenceQuotient.induction N hε ht x f∈
    AsymptoticQuotientIncidence.space N hN hε ht e x at hv
  have hi := (AsymptoticQuotientIncidence.induction_mem_space N hN hε ht e x f).mp hv
  intro hl
  change (space N (gamma d) (gamma_le_of_dvd hd) hε ht x).starProjection
    (AsymptoticCongruenceQuotient.induction N hε ht x f)=0 at hl
  rw [projection_induction] at hl
  have hz : (AsymptoticNestedQuotients.space (gamma_le_of_dvd hd)).starProjection f=0 := by
    apply (AsymptoticCongruenceQuotient.induction N hε ht x).injective
    simpa only [map_zero] using hl
  have hf := AsymptoticNestedQuotients.fricke_projection_zero_of_lower N d hN hd f (sign e.1) hi.1 hz
  change (space N (frickeOldGroup N d hN) (gamma_le_frickeOldGroup hN hd) hε ht x).starProjection
    (AsymptoticCongruenceQuotient.induction N hε ht x f)=0
  rw [projection_induction,hf,map_zero]

theorem simple_incidence_le_newSpace (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : ¬p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x≤
      newSpace (p*M) (gamma M) (frickeOldGroup (p*M) M (Nat.mul_pos hp.pos hM))
        (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) hε ht x := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  intro v hv
  have hl := simple_incidence_lower_projection_zero M p hM hp hpM hε ht e x v hv
  change (v∈quotientSpace (p*M) hε ht x ∧
    (lowerSpace (Nat.dvd_mul_left M p) hε ht x).starProjection v=0) ∧
    (frickeSpace (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p) hε ht x).starProjection v=0
  exact ⟨⟨((AsymptoticQuotientIncidence.space_mem (p*M) (Nat.mul_pos hp.pos hM) hε ht e x v).mp hv).1,hl⟩,
    incidence_fricke_projection_zero_of_lower (p*M) M (Nat.mul_pos hp.pos hM)
      (Nat.dvd_mul_left M p) hε ht e x v hv hl⟩

/-- The original quotient incidence space lies in the local new corner
at every prime factor, for both simple and repeated ramification. -/
theorem prime_incidence_le_newSpace (M p : ℕ) (hM : 0<M) (hp : p.Prime)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x≤
      newSpace (p*M) (gamma M) (frickeOldGroup (p*M) M (Nat.mul_pos hp.pos hM))
        (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) hε ht x := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  by_cases hpM : p∣M
  · exact square_incidence_le_newSpace M p hM hp hpM hε ht e x
  · exact simple_incidence_le_newSpace M p hM hp hpM hε ht e x

#print axioms incidence_fricke_projection_zero_of_lower
#print axioms simple_incidence_le_newSpace
#print axioms prime_incidence_le_newSpace

end AsymptoticCongruenceOldSpace
