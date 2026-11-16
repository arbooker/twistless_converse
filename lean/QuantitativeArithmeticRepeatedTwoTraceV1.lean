module

public import QuantitativeNinaMaassOldDescentV1
public import AsymptoticProjectiveRamifiedCosetsV1
public import QuantitativeArithmeticRepeatedTwoMatricesV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticRamifiedCosets AsymptoticClassicalPetersson QuantitativeMaass
open QuantitativeNinaMaass
open AsymptoticFreshMatrices AsymptoticIntegralSubgroup
open QuantitativeArithmeticRepeatedTwoMatrices

namespace QuantitativeArithmeticRepeatedTwoTrace

/-- At a repeated factor 2 the actual trace has two summands, not three.
The normalization of the associated old projection is consequently 1/2. -/
theorem trace_two (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : AutomorphicL2.representatives (gamma (2*(2*L))) (quotientMeasure (2*(2*L))))
    (z : ℍ) :
    (levelTraceRepresentative (Nat.dvd_mul_left (2*L) 2) f).val z =
      f.val z + f.val ((integralLabel (lowerSL (2*L) 1))⁻¹ • z) := by
  classical
  let := Fintype.ofFinite (gamma (2*L) ⧸ (gamma (2*(2*L))).subgroupOf (gamma (2*L)))
  change (∑ q : gamma (2*L) ⧸ (gamma (2*(2*L))).subgroupOf (gamma (2*L)),
    CosetTrace.value _ f.val _ q z) = _
  rw [← (projectiveCosetEquiv (2*L) 2 (by omega) (by norm_num)
    (Nat.dvd_mul_right 2 L)).sum_comp]
  simp only [Fin.sum_univ_two]
  change f.val ((integralLabel (lowerSL (2*L) 0))⁻¹ • z) +
    f.val ((integralLabel (lowerSL (2*L) 1))⁻¹ • z) = _
  have hz : lowerSL (2*L) 0 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerSL, AsymptoticFreshCRT.lower]
  rw [hz, map_one, inv_one, one_smul]

/-- The reflection in the ordinary old space is a literal single pullback
on representatives. This is the physical trace, not a regular coset model. -/
theorem trace_reflection (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : AutomorphicL2.representatives (gamma (2*(2*L))) (quotientMeasure (2*(2*L))))
    (z : ℍ) :
    2 * ((1/2 : ℂ) * (levelTraceRepresentative (Nat.dvd_mul_left (2*L) 2) f).val z)
      - f.val z = f.val ((integralLabel (lowerSL (2*L) 1))⁻¹ • z) := by
  rw [trace_two L hL f z]
  ring

abbrev Rep (N : ℕ) := AutomorphicL2.representatives (gamma N) (quotientMeasure N)

/-- Reflection obtained from the actual two-coset trace. Its membership
in the automorphic L2 representatives is derived from that trace. -/
def ordinary (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    Module.End ℂ (Rep (2*(2*L))) where
  toFun f := ⟨fun z => f.val ((integralLabel (lowerSL (2*L) 1))⁻¹ • z), by
    let v := levelCoverRepresentative (Nat.dvd_mul_left (2*L) 2)
      (levelTraceRepresentative (Nat.dvd_mul_left (2*L) 2) f) - f
    have he : v.val = fun z => f.val ((integralLabel (lowerSL (2*L) 1))⁻¹ • z) := by
      funext z
      change (levelTraceRepresentative (Nat.dvd_mul_left (2*L) 2) f).val z - f.val z = _
      rw [trace_two L hL f z]
      ring
    rw [← he]
    exact v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ordinary_apply (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : Rep (2*(2*L))) (z : ℍ) :
    (ordinary L hL f).val z = f.val ((integralLabel (lowerSL (2*L) 1))⁻¹ • z) := rfl

/-- The Fricke-conjugate of the ordinary old reflection. -/
def conjugate (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    Module.End ℂ (Rep (2*(2*L))) :=
  (QuantitativeNinaMaass.frickeRepresentative (2*(2*L)) (by omega)).comp
    ((ordinary L hL).comp (QuantitativeNinaMaass.frickeRepresentative (2*(2*L)) (by omega)))

theorem conjugate_apply (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : Rep (2*(2*L))) (z : ℍ) :
    (conjugate L hL f).val z = f.val ((translationLabel (-1/2))⁻¹ • z) := by
  change f.val (frickeLabel (2*(2*L)) (by omega) •
    ((integralLabel (lowerSL (2*L) 1))⁻¹ • (frickeLabel (2*(2*L)) (by omega) • z))) = _
  have hc : frickeLabel (2*(2*L)) (by omega) * integralLabel (lowerSL (2*L) 1) *
      frickeLabel (2*(2*L)) (by omega) = translationLabel (-1/2) := by
    rw [fricke_half L hL, mul_assoc, frickeLabel_mul_self, mul_one]
  have hi := congrArg (fun g => g⁻¹) hc
  simp only [mul_inv_rev, frickeLabel_inv] at hi
  rw [← mul_smul, ← mul_smul, mul_assoc, hi]

/-- Pullback powers preserve the literal group word, on representatives. -/
theorem pullback_pow {N : ℕ} (A : Module.End ℂ (Rep N))
    (g : AsymptoticRationalGroup.Group)
    (hA : ∀ f z, (A f).val z = f.val (g⁻¹ • z)) (n : ℕ) :
    ∀ f z, ((A^n) f).val z = f.val ((g^n)⁻¹ • z) := by
  induction n with
  | zero => intro f z; simp
  | succ n ih =>
    intro f z
    rw [pow_succ, Module.End.mul_apply, ih, hA, pow_succ, mul_inv_rev, mul_smul]

theorem pullback_pow_eq_one {N : ℕ} (A : Module.End ℂ (Rep N))
    (g : AsymptoticRationalGroup.Group)
    (hA : ∀ f z, (A f).val z = f.val (g⁻¹ • z)) (n : ℕ)
    (hn : g^n ∈ gamma N) : A^n = 1 := by
  ext f z
  rw [pullback_pow A g hA n]
  exact f.property.2.1 ⟨(g^n)⁻¹, (gamma N).inv_mem hn⟩ z

theorem ordinary_square (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    ordinary L hL * ordinary L hL = 1 := by
  simpa only [pow_two] using pullback_pow_eq_one (ordinary L hL)
    (integralLabel (lowerSL (2*L) 1)) (ordinary_apply L hL) 2 (lower_square L)

theorem conjugate_square (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    conjugate L hL * conjugate L hL = 1 := by
  have hw : QuantitativeNinaMaass.frickeRepresentative (2*(2*L)) (by omega) *
      QuantitativeNinaMaass.frickeRepresentative (2*(2*L)) (by omega) = 1 := by
    ext f z
    change f.val (frickeLabel (2*(2*L)) (by omega) •
      (frickeLabel (2*(2*L)) (by omega) • z)) = f.val z
    rw [← mul_smul, frickeLabel_mul_self, one_smul]
  change (_ * (ordinary L hL * _)) * (_ * (ordinary L hL * _)) = 1
  have hww (x : Module.End ℂ (Rep (2*(2*L)))) :
      QuantitativeNinaMaass.frickeRepresentative (2*(2*L)) (by omega) *
        (QuantitativeNinaMaass.frickeRepresentative (2*(2*L)) (by omega) * x) = x := by
    simpa only [mul_assoc, one_mul] using congrArg (fun a : Module.End ℂ (Rep (2*(2*L))) => a*x) hw
  have hrr (x : Module.End ℂ (Rep (2*(2*L)))) : ordinary L hL * (ordinary L hL * x) = x := by
    simpa only [mul_assoc, one_mul] using congrArg (fun a : Module.End ℂ (Rep (2*(2*L))) => a*x) (ordinary_square L hL)
  simp only [mul_assoc, hww, hrr, hw]

theorem product_apply (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : Rep (2*(2*L))) (z : ℍ) :
    ((ordinary L hL * conjugate L hL) f).val z =
      f.val ((integralLabel (lowerSL (2*L) 1) * translationLabel (-1/2))⁻¹ • z) := by
  rw [Module.End.mul_apply, ordinary_apply, conjugate_apply, mul_inv_rev, mul_smul]

theorem even_product (t : ℕ) (ht : 0 < t) [NeZero (2*(2*(2*t)))] :
    (ordinary (2*t) (by omega) * conjugate (2*t) (by omega))^2 = 1 :=
  pullback_pow_eq_one _ _ (product_apply (2*t) (by omega)) 2 (even_word t)

theorem odd_product (t : ℕ) [NeZero (2*(2*(2*t+1)))] :
    (ordinary (2*t+1) (by omega) * conjugate (2*t+1) (by omega))^3 = 1 :=
  pullback_pow_eq_one _ _ (product_apply (2*t+1) (by omega)) 3 (odd_word t)

#print axioms trace_two
#print axioms trace_reflection
#print axioms ordinary_square
#print axioms conjugate_square
#print axioms even_product
#print axioms odd_product

end QuantitativeArithmeticRepeatedTwoTrace
