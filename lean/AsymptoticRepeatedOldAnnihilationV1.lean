module

public import AsymptoticRamifiedOldBranchesV1
public import AsymptoticQuotientIncidenceSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedCosets

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticOrbitDecode
open scoped lp

/-- At a repeated factor, the actual ramified branch equation is the
vanishing of the second old projection. -/
theorem fricke_projection_zero_of_ramified_zero (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M)
    (f : ℓ²(Classes (gamma (q*M)),ℂ))
    (hf : ∀ g,∑ a : Fin q,f (classOf (gamma (q*M)) (ramifiedLabel q hq a*g))=0) :
    (space (gamma_le_frickeOldGroup (Nat.mul_pos hq hM) (Nat.dvd_mul_left M q))).starProjection f=0 := by
  apply (projection_eq_zero_iff_coset_sums
    (gamma_le_frickeOldGroup (Nat.mul_pos hq hM) (Nat.dvd_mul_left M q))
    (frickeRepresentative M q hM hq) (frickeCosetEquiv M q hM hq hqM) (fun _ => rfl) f).mpr
  intro g
  simp only [frickeRepresentative_inv]
  have he := hf (dilationLabel q hq*g)
  simpa only [← mul_assoc,ramifiedLabel_mul_dilation] using he

#print axioms fricke_projection_zero_of_ramified_zero

end AsymptoticRamifiedCosets

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticSectorSigns AsymptoticOrbitDecode
open scoped lp

/-- The closed incidence space obtained from original Euler equations
has zero second old trace at every square-dividing prime. -/
theorem square_incidence_fricke_projection_zero (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : v∈AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x) :
    (frickeSpace (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p) hε ht x).starProjection v=0 := by
  have hq := ((AsymptoticQuotientIncidence.space_mem (p*M) (Nat.mul_pos hp.pos hM) hε ht e x v).mp hv).1
  obtain ⟨f,rfl⟩ := hq
  change AsymptoticCongruenceQuotient.induction (p*M) hε ht x f∈
    AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x at hv
  have hi := (AsymptoticQuotientIncidence.induction_mem_space (p*M) (Nat.mul_pos hp.pos hM)
    hε ht e x f).mp hv
  have hs : p^2∣p*M := by
    rw [pow_two]
    exact Nat.mul_dvd_mul_left p hpM
  have hr : ∀ g,∑ a : Fin p,f (classOf (p*M) (ramifiedLabel p hp.pos a*g))=0 := by
    intro g
    have he := hi.2 ⟨p,hp,Nat.dvd_mul_right p M⟩ g
    simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_left hs,zero_mul] using he
  have hz := AsymptoticRamifiedCosets.fricke_projection_zero_of_ramified_zero M p hM hp.pos hpM f hr
  change (space (p*M) (frickeOldGroup (p*M) M (Nat.mul_pos hp.pos hM))
    (gamma_le_frickeOldGroup (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) hε ht x).starProjection
    (AsymptoticCongruenceQuotient.induction (p*M) hε ht x f)=0
  rw [projection_induction,hz,map_zero]

#print axioms square_incidence_fricke_projection_zero

end AsymptoticCongruenceOldSpace
