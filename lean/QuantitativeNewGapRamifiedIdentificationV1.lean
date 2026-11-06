module

public import AsymptoticSimpleOldAnnihilationV1
public import AsymptoticQuotientNewSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticAtkinLehner AsymptoticFreshMatrices AsymptoticQuotientOperators
open AsymptoticOrbitDecode
open scoped lp

/-- Converse to the existing incidence-to-local-sign implication:
the literal old trace and local Atkin sign imply the original ramified
equation, using the actual finite trace representatives. -/
theorem lower_zero_local_sign_ramified (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (f : ℓ²(Classes (gamma (p*M)),ℂ)) (s : ℂ) (hs : s^2=1)
    (hP : letI : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
      (space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection f=0)
    (hW : ∀ g,f (classOf (gamma (p*M))
      (localAtkin M p hM (Fact.out : p.Prime).pos A B hAB*g))=
        s*f (classOf (gamma (p*M)) g)) (g : AsymptoticRationalGroup.Group) :
    ∑ a : Fin p,f (classOf (gamma (p*M))
      (ramifiedLabel p (Fact.out : p.Prime).pos a*g))=
      -s*f (classOf (gamma (p*M)) g) := by
  let : NeZero (p*M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
  have htrace := (projection_eq_zero_iff_coset_sums
    (gamma_le_of_dvd (Nat.dvd_mul_left M p))
    (traceRepresentative M p A B hAB) (traceCosetEquiv M p hM hpM A B hAB)
    (fun _ => rfl) f).mp hP g
  rw [Fintype.sum_option] at htrace
  simp only [traceRepresentative,Subgroup.coe_one,inv_one,one_mul,inv_inv] at htrace
  simp_rw [← localAtkin_mul_ramified M p hM (Fact.out : p.Prime).pos A B hAB,
    mul_assoc,hW] at htrace
  rw [← Finset.mul_sum] at htrace
  linear_combination s*htrace-
    (∑ a : Fin p,f (classOf (gamma (p*M))
      (ramifiedLabel p (Fact.out : p.Prime).pos a*g)))*hs

#print axioms lower_zero_local_sign_ramified

/-- At repeated primes, vanishing of the literal second-old projection
is exactly the original zero ramified equation. -/
theorem fricke_zero_ramified_zero (M p : ℕ) (hM : 0<M) (hp : 0<p) (hpM : p∣M)
    (f : ℓ²(Classes (gamma (p*M)),ℂ))
    (hP : (space (gamma_le_frickeOldGroup (Nat.mul_pos hp hM)
      (Nat.dvd_mul_left M p))).starProjection f=0) (g : AsymptoticRationalGroup.Group) :
    ∑ a : Fin p,f (classOf (gamma (p*M)) (ramifiedLabel p hp a*g))=0 := by
  have htrace := (projection_eq_zero_iff_coset_sums
    (gamma_le_frickeOldGroup (Nat.mul_pos hp hM) (Nat.dvd_mul_left M p))
    (AsymptoticRamifiedCosets.frickeRepresentative M p hM hp)
    (AsymptoticRamifiedCosets.frickeCosetEquiv M p hM hp hpM) (fun _ => rfl) f).mp hP
      ((dilationLabel p hp)⁻¹*g)
  simpa only [AsymptoticRamifiedCosets.frickeRepresentative_inv,
    ← ramifiedLabel_mul_dilation p hp,mul_assoc,mul_inv_cancel_left] using htrace

#print axioms fricke_zero_ramified_zero

end QuantitativeNewGap
