module

public import AsymptoticAtkinLehnerTraceCosetsV1
public import AsymptoticRepeatedOldAnnihilationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticAtkinLehner

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticOrbitDecode AsymptoticFreshMatrices
open scoped lp

/-- The first old projection vanishes at a prime dividing the level
exactly once. All local signs and coset trace identities are derived. -/
theorem simple_lower_projection_zero (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M)
    (f : ℓ²(Classes (gamma (p*M)),ℂ)) (w δ : ℂ) (hδ : δ^2=1)
    (hW : ∀ g,w*f (classOf (gamma (p*M)) (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*g))=
      f (classOf (gamma (p*M)) g))
    (hU : ∀ g,∑ a : Fin p,f (classOf (gamma (p*M)) (ramifiedLabel p (Fact.out : p.Prime).pos a*g))=
      δ*f (classOf (gamma (p*M)) g)) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
    (space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection f=0 := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
  have hc : p.Coprime M := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have hab : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    have he := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at he
    exact he.symm
  apply (projection_eq_zero_iff_coset_sums (gamma_le_of_dvd (Nat.dvd_mul_left M p))
    (traceRepresentative M p (Nat.gcdA p M) (Nat.gcdB p M) hab)
    (traceCosetEquiv M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hab) (fun _ => rfl) f).mpr
  intro g
  rw [Fintype.sum_option]
  simp only [traceRepresentative,Subgroup.coe_one,inv_one,one_mul,inv_inv]
  exact old_trace_zero M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hab
    (fun a => f (classOf (gamma (p*M)) a))
    (fun a g => congrArg f (classOf_mul (gamma (p*M)) a g)) w δ hδ hW hU g

#print axioms simple_lower_projection_zero

end AsymptoticAtkinLehner

namespace AsymptoticSectorSigns

theorem delta_sq {N : ℕ} (e : Sector N) (p : ℕ) : delta e p^2=1 := by
  unfold delta
  split_ifs
  · exact sign_sq _
  · norm_num

#print axioms delta_sq

end AsymptoticSectorSigns

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticSectorSigns AsymptoticOrbitDecode
open scoped lp

theorem simple_incidence_lower_projection_zero (M p : ℕ) (hM : 0<M) (hp : p.Prime) (hpM : ¬p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (e : Sector (p*M)) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : v∈AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x) :
    letI : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    (lowerSpace (Nat.dvd_mul_left M p) hε ht x).starProjection v=0 := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  have hq := ((AsymptoticQuotientIncidence.space_mem (p*M) (Nat.mul_pos hp.pos hM) hε ht e x v).mp hv).1
  obtain ⟨f,rfl⟩ := hq
  change AsymptoticCongruenceQuotient.induction (p*M) hε ht x f∈
    AsymptoticQuotientIncidence.space (p*M) (Nat.mul_pos hp.pos hM) hε ht e x at hv
  have hi := (AsymptoticQuotientIncidence.induction_mem_space (p*M) (Nat.mul_pos hp.pos hM)
    hε ht e x f).mp hv
  have hs : ¬p^2∣p*M := by
    rw [pow_two,Nat.mul_dvd_mul_iff_left hp.pos]
    exact hpM
  have hr : ∀ g,∑ a : Fin p,f (classOf (p*M) (ramifiedLabel p hp.pos a*g))=
      delta e p*f (classOf (p*M) g) := by
    intro g
    have he := hi.2 ⟨p,hp,Nat.dvd_mul_right p M⟩ g
    simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hs] using he
  have hz := AsymptoticAtkinLehner.simple_lower_projection_zero M p hM hpM f
    (sign e.1) (delta e p) (delta_sq e p) hi.1 hr
  change (space (p*M) (gamma M) (gamma_le_of_dvd (Nat.dvd_mul_left M p)) hε ht x).starProjection
    (AsymptoticCongruenceQuotient.induction (p*M) hε ht x f)=0
  rw [projection_induction,hz,map_zero]

#print axioms simple_incidence_lower_projection_zero

end AsymptoticCongruenceOldSpace
