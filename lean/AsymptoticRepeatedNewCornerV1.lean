module

public import AsymptoticRepeatedBothOldV1
public import AsymptoticCongruenceNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticSectorSigns AsymptoticRegularTrace
open scoped lp

/-- Square-dividing Euler incidence equations place the quotient vector
in the actual corner orthogonal to both old degeneracy ranges. -/
theorem square_incidence_le_newSpace (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x≤
      newSpace (p*M) (gamma M) (frickeOldGroup (p*M) M (Nat.mul_pos hp.pos hM))
        (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) hε ht x := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  intro v hv
  change (v∈quotientSpace (p*M) hε ht x ∧
    (lowerSpace (Nat.dvd_mul_left M p) hε ht x).starProjection v=0) ∧
    (frickeSpace (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p) hε ht x).starProjection v=0
  exact ⟨⟨((AsymptoticQuotientIncidence.space_mem (p*M) (Nat.mul_pos hp.pos hM) hε ht e x v).mp hv).1,
    square_incidence_lower_projection_zero M p hM hp hpM hε ht e x v hv⟩,
    square_incidence_fricke_projection_zero M p hM hp hpM hε ht e x v hv⟩

#print axioms square_incidence_le_newSpace

end AsymptoticCongruenceOldSpace
