module

public import AsymptoticRepeatedOldAnnihilationV1
public import AsymptoticProjectiveRamifiedCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticRamifiedCosets

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticOrbitDecode AsymptoticFreshMatrices AsymptoticIntegralSubgroup
open scoped lp

theorem lower_projection_zero_of_ramified_zero (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M)
    (f : ℓ²(Classes (gamma (q*M)),ℂ)) (s : ℂ)
    (hF : ∀ g,s*f (classOf (gamma (q*M)) (frickeLabel (q*M) (Nat.mul_pos hq hM)*g))=
      f (classOf (gamma (q*M)) g))
    (hf : ∀ g,∑ a : Fin q,f (classOf (gamma (q*M)) (ramifiedLabel q hq a*g))=0) :
    letI : NeZero (q*M) := ⟨(Nat.mul_pos hq hM).ne'⟩
    (space (gamma_le_of_dvd (Nat.dvd_mul_left M q))).starProjection f=0 := by
  let : NeZero (q*M) := ⟨(Nat.mul_pos hq hM).ne'⟩
  apply (projection_eq_zero_iff_coset_sums (gamma_le_of_dvd (Nat.dvd_mul_left M q))
    (projectiveRepresentative M q) (projectiveCosetEquiv M q hM hq hqM) (fun _ => rfl) f).mpr
  intro g
  have he : ∀ j : Fin q,frickeLabel (q*M) (Nat.mul_pos hq hM)*(projectiveRepresentative M q j).val⁻¹=
      translationLabel ((j.val:ℚ)/q)*frickeLabel (q*M) (Nat.mul_pos hq hM) := by
    intro j
    change frickeLabel (q*M) _*(integralLabel (lowerSL M (j.val:ℤ)))⁻¹=_
    rw [← map_inv,lowerSL_inv]
    simpa using fricke_lower_div M q hM hq (-(j.val:ℤ))
  have hu : (∑ j : Fin q,f (classOf (gamma (q*M))
      (translationLabel ((j.val:ℚ)/q)*(frickeLabel (q*M) (Nat.mul_pos hq hM)*g))))=0 := by
    simpa only [← mul_assoc,ramifiedLabel_mul_dilation] using
      hf (dilationLabel q hq*(frickeLabel (q*M) (Nat.mul_pos hq hM)*g))
  calc
    _ = ∑ j : Fin q,s*f (classOf (gamma (q*M))
        (frickeLabel (q*M) (Nat.mul_pos hq hM)*((projectiveRepresentative M q j).val⁻¹*g))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (hF _).symm
    _ = s*(∑ j : Fin q,f (classOf (gamma (q*M))
        (translationLabel ((j.val:ℚ)/q)*(frickeLabel (q*M) (Nat.mul_pos hq hM)*g)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc,he,mul_assoc]
    _ = 0 := by rw [hu,mul_zero]

#print axioms lower_projection_zero_of_ramified_zero

end AsymptoticRamifiedCosets

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticSectorSigns AsymptoticOrbitDecode
open scoped lp

theorem square_incidence_lower_projection_zero (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : v∈AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    (lowerSpace (Nat.dvd_mul_left M p) hε ht x).starProjection v=0 := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
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
  have hz := AsymptoticRamifiedCosets.lower_projection_zero_of_ramified_zero M p hM hp.pos hpM f
    (sign e.1) hi.1 hr
  change (space (p*M) (gamma M) (gamma_le_of_dvd (Nat.dvd_mul_left M p)) hε ht x).starProjection
    (AsymptoticCongruenceQuotient.induction (p*M) hε ht x f)=0
  rw [projection_induction,hz,map_zero]

#print axioms square_incidence_lower_projection_zero

end AsymptoticCongruenceOldSpace
