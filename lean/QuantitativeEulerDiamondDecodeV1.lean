module

public import QuantitativeEulerDiamondDefectV1
public import AsymptoticOrbitDecodeV1
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticIntegralSubgroup AsymptoticOrbitDecode
open QuantitativeEulerDiamondPolynomial
open AsymptoticRegularCompactBranch (Space)

abbrev G := AsymptoticRationalGroup.Group
abbrev Ring := MonoidAlgebra ℂ G

def symbol : G →* Ring := MonoidAlgebra.of ℂ G

def evaluate (f : G → ℂ) : Ring →+ ℂ :=
  (Finsupp.linearCombination ℂ f).toAddMonoidHom.comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

@[simp] theorem evaluate_symbol (f : G → ℂ) (g : G) : evaluate f (symbol g)=f g := by
  simp [evaluate,symbol,MonoidAlgebra.of_apply]

@[simp] theorem evaluate_one (f : G → ℂ) : evaluate f 1=f 1 := by
  simpa only [map_one] using evaluate_symbol f 1

theorem evaluate_smul (f : G → ℂ) (c : ℂ) (A : Ring) :
    evaluate f (c • A)=c*evaluate f A := by
  change Finsupp.linearCombination ℂ f (c • A.coeff)=_
  rw [map_smul]
  rfl

/-- Evaluation is the actual right action on group-coordinate functions,
without any summability or modular-invariance assumption on the function. -/
theorem evaluate_left_symbol (f : G → ℂ) (g : G) (A : Ring) :
    evaluate f (symbol g*A)=evaluate (fun h => f (g*h)) A := by
  induction A using MonoidAlgebra.induction_on with
  | of a =>
    change evaluate f (symbol g*symbol a)=evaluate (fun h => f (g*h)) (symbol a)
    rw [←map_mul,evaluate_symbol,evaluate_symbol]
  | add A B hA hB => simp only [mul_add,map_add,hA,hB]
  | smul c A hA => rw [mul_smul_comm,evaluate_smul,evaluate_smul,hA]

theorem evaluate_period_relation (f : G → ℂ) (T : G)
    (hf : ∀ a, f (T*a)=f a) (A : Ring) :
    evaluate f ((symbol T-1)*A)=0 := by
  rw [sub_mul,one_mul,map_sub,evaluate_left_symbol]
  have he : (fun a => f (T*a))=f := funext hf
  rw [he,sub_self]

theorem translationLabel_pow (r : ℚ) (n : ℕ) :
    translationLabel r^n=translationLabel ((n : ℚ)*r) := by
  have hz : translationLabel 0=1 := by
    have h := translationLabel_mul 0 0
    simpa only [zero_add,mul_eq_left] using h
  induction n with
  | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul] using hz.symm
  | succ n ih =>
    rw [pow_succ,ih,translationLabel_mul]
    congr 1
    push_cast
    ring

theorem translation_fraction_period (ℓ : ℕ) (hℓ : ℓ≠0) :
    translationLabel ((ℓ : ℚ)⁻¹)^ℓ=translationLabel 1 := by
  rw [translationLabel_pow,mul_inv_cancel₀ (by exact_mod_cast hℓ)]

def decodedEvaluation (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a : G) : Ring →+ ℂ :=
  evaluate (fun g => decode ε t x v (g*a))

@[simp] theorem decodedEvaluation_symbol (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a g : G) :
    decodedEvaluation ε t x v a (symbol g)=decode ε t x v (g*a) :=
  evaluate_symbol _ _

/-- Periodicity is discharged by the actual strip fold used in the
regular representation; it is not an extra hypothesis on the vector. -/
theorem decodedEvaluation_periodic (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a : G)
    (ℓ : ℕ) (hℓ : ℓ≠0) (A : Ring) :
    decodedEvaluation ε t x v a ((symbol (translationLabel ((ℓ : ℚ)⁻¹))^ℓ-1)*A)=0 := by
  rw [←map_pow,translation_fraction_period ℓ hℓ]
  apply evaluate_period_relation
  intro g
  simpa only [mul_assoc,Int.cast_one] using decode_periodic ε t x v (g*a) 1

/-- The exact diamond inverse now acts on the literal decoded orbit
vector, including its automatic periodic folding. The branch labels are
actual positive rational projective transformations. -/
theorem decoded_diamond_recovery (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space) (a : G)
    (ℓ : ℕ) (hℓ : 2≤ℓ) (w : ℂ) (g : G) (branches : ℕ → G) :
    let X := symbol (translationLabel ((ℓ : ℚ)⁻¹))
    let W : Ring := w • 1
    let P := Polynomial.aeval X (inversePolynomial ℓ)
    let Q := Polynomial.aeval X (correctionPolynomial ℓ)
    let F := decodedEvaluation ε t x v a
    w*decode ε t x v (g*a)-decode ε t x v a=
      F (averagedResidual X W (fun j => symbol (branches j)) ℓ*P)-
      F (congruenceCorrection X W (symbol g) (symbol g⁻¹) (fun j => symbol (branches j)) ℓ*P)-
      F (W*(symbol g*X^ℓ*symbol g⁻¹-1)*symbol g*Q) := by
  dsimp
  have hig : symbol g⁻¹*symbol g=1 := by rw [←map_mul,inv_mul_cancel,map_one]
  have h := periodic_diamond_recovery
    (symbol (translationLabel ((ℓ : ℚ)⁻¹))) (w • (1 : Ring))
    (symbol g) (symbol g⁻¹) hig (fun j => symbol (branches j)) ℓ hℓ
    (decodedEvaluation ε t x v a)
    (decodedEvaluation_periodic ε t x v a ℓ (by omega))
  simpa only [smul_mul_assoc,one_mul,map_sub,decodedEvaluation,evaluate_smul,
    evaluate_symbol,evaluate_one] using h

#print axioms evaluate_left_symbol
#print axioms decodedEvaluation_periodic
#print axioms decoded_diamond_recovery
end QuantitativeEulerDiamondDecode
