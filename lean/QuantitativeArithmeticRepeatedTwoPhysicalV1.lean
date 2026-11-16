module

public import QuantitativeArithmeticRepeatedTwoTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticCongruenceStrip QuantitativeMaass QuantitativeNinaMaass
open QuantitativeArithmeticRepeatedTwoTrace

namespace QuantitativeArithmeticRepeatedTwoPhysical

/-- Twice the ordinary old projection minus the identity, on the actual
completed automorphic Hilbert space at level 4L. -/
def ordinaryOperator (L : ℕ) [NeZero (2*(2*L))] :
    AutomorphicSpace (2*(2*L)) →L[ℂ] AutomorphicSpace (2*(2*L)) :=
  (levelCover (Nat.dvd_mul_left (2*L) 2)).comp
    (levelTrace (Nat.dvd_mul_left (2*L) 2)) - ContinuousLinearMap.id ℂ _

def conjugateOperator (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    AutomorphicSpace (2*(2*L)) →L[ℂ] AutomorphicSpace (2*(2*L)) :=
  (frickeIsometry (2*(2*L)) (by omega)).toContinuousLinearMap.comp
    ((ordinaryOperator L).comp (frickeIsometry (2*(2*L)) (by omega)).toContinuousLinearMap)

theorem ordinary_embedding (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : Rep (2*(2*L))) :
    ordinaryOperator L (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (ordinary L hL f) := by
  change levelCover _ (levelTrace _ (AutomorphicL2.denseEmbedding _ _ f)) -
    AutomorphicL2.denseEmbedding _ _ f = _
  rw [levelTraceRepresentative_embedding, levelCover_apply, ← map_sub]
  congr 1
  apply Subtype.ext
  funext z
  change (levelTraceRepresentative (Nat.dvd_mul_left (2*L) 2) f).val z - f.val z = _
  rw [trace_two L hL f z]
  change f.val z + f.val _ - f.val z = f.val _
  ring

theorem conjugate_embedding (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : Rep (2*(2*L))) :
    conjugateOperator L hL (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (conjugate L hL f) := by
  change frickeIsometry _ _ (ordinaryOperator L
    (frickeIsometry _ _ (AutomorphicL2.denseEmbedding _ _ f))) = _
  rw [frickeIsometry_apply, ordinary_embedding L hL, frickeIsometry_apply]
  rfl

/-- Transfer polynomial identities through the genuine dense embedding;
no regular-representation or finite-dimensional surrogate is used. -/
theorem power_embedding {N : ℕ}
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (B : Module.End ℂ (Rep N))
    (h : ∀ f, A (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (B f)) (n : ℕ) (f : Rep N) :
    (A^n) (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ ((B^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, h, ih, pow_succ, Module.End.mul_apply]

theorem power_eq_one {N : ℕ}
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (B : Module.End ℂ (Rep N))
    (h : ∀ f, A (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (B f)) (n : ℕ) (hn : B^n = 1) : A^n = 1 := by
  apply DFunLike.coe_injective
  apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
    (A^n).continuous (1 : AutomorphicSpace N →L[ℂ] AutomorphicSpace N).continuous
  funext f
  change (A^n) (AutomorphicL2.denseEmbedding _ _ f) = AutomorphicL2.denseEmbedding _ _ f
  rw [power_embedding A B h, hn]
  rfl

theorem ordinary_square (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    ordinaryOperator L * ordinaryOperator L = 1 := by
  simpa only [pow_two] using power_eq_one (ordinaryOperator L) (ordinary L hL)
    (ordinary_embedding L hL) 2 (by simpa only [pow_two] using
      QuantitativeArithmeticRepeatedTwoTrace.ordinary_square L hL)

theorem conjugate_square (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))] :
    conjugateOperator L hL * conjugateOperator L hL = 1 := by
  simpa only [pow_two] using power_eq_one (conjugateOperator L hL) (conjugate L hL)
    (conjugate_embedding L hL) 2 (by simpa only [pow_two] using
      QuantitativeArithmeticRepeatedTwoTrace.conjugate_square L hL)

theorem product_embedding (L : ℕ) (hL : 0 < L) [NeZero (2*(2*L))]
    (f : Rep (2*(2*L))) :
    (ordinaryOperator L * conjugateOperator L hL) (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ ((ordinary L hL * conjugate L hL) f) := by
  rw [mul_apply_eq_comp, conjugate_embedding, ordinary_embedding L hL]
  rfl

theorem even_annihilator (t : ℕ) (ht : 0 < t) [NeZero (2*(2*(2*t)))] :
    (ordinaryOperator (2*t) + conjugateOperator (2*t) (by omega))^4 -
      4*(ordinaryOperator (2*t) + conjugateOperator (2*t) (by omega))^2 = 0 := by
  apply QuantitativeArithmeticTwoInvolutionPolynomial.square_product
    (ordinaryOperator (2*t)) (conjugateOperator (2*t) (by omega))
    (ordinary_square (2*t) (by omega)) (conjugate_square (2*t) (by omega))
  exact power_eq_one _ _ (product_embedding (2*t) (by omega)) 2 (even_product t ht)

theorem odd_annihilator (t : ℕ) [NeZero (2*(2*(2*t+1)))] :
    (ordinaryOperator (2*t+1) + conjugateOperator (2*t+1) (by omega))^4 -
      5*(ordinaryOperator (2*t+1) + conjugateOperator (2*t+1) (by omega))^2 + 4 = 0 := by
  apply QuantitativeArithmeticTwoInvolutionPolynomial.cube_product
    (ordinaryOperator (2*t+1)) (conjugateOperator (2*t+1) (by omega))
    (ordinary_square (2*t+1) (by omega)) (conjugate_square (2*t+1) (by omega))
  exact power_eq_one _ _ (product_embedding (2*t+1) (by omega)) 3 (odd_product t)

#print axioms ordinary_embedding
#print axioms conjugate_embedding
#print axioms ordinary_square
#print axioms conjugate_square
#print axioms even_annihilator
#print axioms odd_annihilator

end QuantitativeArithmeticRepeatedTwoPhysical
