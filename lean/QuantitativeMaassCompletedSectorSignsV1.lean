module

public import QuantitativeMaassNewSpaceReconstructionV1
public import QuantitativeMaassNewSignSmoothingV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNinaMaass QuantitativeNewGap

namespace QuantitativeMaass

def frickeGeneratorIndex (N : ℕ) (hN : 0<N) : admissibleGeneratorIndex N hN :=
  ⟨frickeLabel N hN,admissibleNormalizerGenerator.fricke⟩

def simpleAtkinGeneratorIndex (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    admissibleGeneratorIndex N hN :=
  ⟨exactAtkinLabel (N/p.val) p.val (simplePrime_prime p).pos
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p),
    admissibleNormalizerGenerator.atkin (N/p.val) p.val (simplePrime_prime p).pos
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)
      (Nat.mul_div_cancel' (simplePrime_dvd p))⟩

theorem simpleAtkinGeneratorIndex_value (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    (simpleAtkinGeneratorIndex N hN p).val=localAtkinLabel N hN p :=
  exactAtkinLabel_eq_localAtkin (N/p.val) p.val (simplePrime_colevel_pos N hN p)
    (simplePrime_prime p).pos (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val))
    (simplePrime_bezout N p)

/-- The completed generator equations give the literal pointwise sector
equations on every continuous representative in the sector. -/
theorem completedNewSign_continuous_sector (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN → ℂ) (e : Sector N)
    (hχW : χ (frickeGeneratorIndex N hN)=sign e.1)
    (hχS : ∀ p : SimplePrime N,χ (simpleAtkinGeneratorIndex N hN p)= -delta e p.val)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hx : AutomorphicL2.denseEmbedding _ _ f∈completedNewSignSpace N hN χ) :
    (∀ z,sign e.1*f.val (frickeLabel N hN • z)=f.val z) ∧
    (∀ p : SimplePrime N,∀ z,f.val (localAtkinLabel N hN p • z)= -delta e p.val*f.val z) := by
  constructor
  · intro z
    have he := normalizer_eigen_continuous N
      (admissibleGeneratorLift N hN (frickeGeneratorIndex N hN)) f hf
      (χ (frickeGeneratorIndex N hN)) (hx.2.2 (frickeGeneratorIndex N hN)) z
    change f.val (frickeLabel N hN • z)=χ (frickeGeneratorIndex N hN)*f.val z at he
    rw [hχW] at he
    rw [he,←mul_assoc,←pow_two,sign_sq,one_mul]
  · intro p z
    have he := normalizer_eigen_continuous N
      (admissibleGeneratorLift N hN (simpleAtkinGeneratorIndex N hN p)) f hf
      (χ (simpleAtkinGeneratorIndex N hN p)) (hx.2.2 (simpleAtkinGeneratorIndex N hN p)) z
    change f.val ((simpleAtkinGeneratorIndex N hN p).val • z)=
      χ (simpleAtkinGeneratorIndex N hN p)*f.val z at he
    simpa only [simpleAtkinGeneratorIndex_value,hχS] using he

#print axioms simpleAtkinGeneratorIndex_value
#print axioms completedNewSign_continuous_sector

end QuantitativeMaass
