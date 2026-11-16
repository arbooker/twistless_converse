module

public import QuantitativeMaassCountingLocalExpressionV1
public import AsymptoticProjectiveRamifiedCosetsV1
public import QuantitativeArithmeticRepeatedTwoMatricesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticCongruenceLabels
open AsymptoticRamifiedCosets AsymptoticFreshMatrices AsymptoticIntegralSubgroup
open QuantitativeNewGap ContinuousLinearMap
open scoped lp
namespace QuantitativeMaass.Counting

/-- Evaluate the actual unnormalized old trace using any proved coset
representative system. The relative-index normalization cancels exactly. -/
theorem coverTraceOperator_cosets {M N : ℕ} [NeZero N] (hMN : M∣N)
    {ι : Type*} [Fintype ι] (r : ι→gamma M)
    (e : ι≃(gamma M ⧸ (gamma N).subgroupOf (gamma M)))
    (he : ∀ i,e i=QuotientGroup.mk (r i)) (f : Space N) (g : G) :
    coverTraceOperator hMN f (classOf (gamma N) g)=
      ∑ i,f (classOf (gamma N) ((r i).val⁻¹*g)) := by
  have hn : (((gamma N).subgroupOf (gamma M)).index:ℂ)≠0 := by
    exact_mod_cast (index_pos (H:=gamma N) (J:=gamma M)).ne'
  change (((gamma N).subgroupOf (gamma M)).index:ℂ)*
    (space (gamma_le_of_dvd hMN)).starProjection f (classOf (gamma N) g)=_
  rw [projection_apply,forget_classOf,fibre_sum_eq_coset_sum _ r e he]
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]

def repeatedOrdinary (L : ℕ) [NeZero (2*(2*L))] : Space (2*(2*L))→L[ℂ]Space (2*(2*L)) :=
  coverTraceOperator (Nat.dvd_mul_left (2*L) 2)-1

def repeatedConjugate (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    Space (2*(2*L))→L[ℂ]Space (2*(2*L)) :=
  let W := normalizerOperator (2*(2*L)) (completedFrickeNormalizer (2*(2*L)) (by omega))
  W.comp ((repeatedOrdinary L).comp W)

theorem repeatedOrdinary_apply (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))]
    (f : Space (2*(2*L))) (g : G) :
    repeatedOrdinary L f (classOf (gamma (2*(2*L))) g)=
      f (classOf (gamma (2*(2*L))) ((integralLabel (lowerSL (2*L) 1))⁻¹*g)) := by
  have hh := coverTraceOperator_cosets (Nat.dvd_mul_left (2*L) 2)
    (projectiveRepresentative (2*L) 2)
    (projectiveCosetEquiv (2*L) 2 (by omega) (by norm_num) (Nat.dvd_mul_right 2 L))
    (fun _ => rfl) f g
  rw [Fin.sum_univ_two] at hh
  have hz : lowerSL (2*L) 0=1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerSL,AsymptoticFreshCRT.lower]
  change coverTraceOperator (Nat.dvd_mul_left (2*L) 2) f (classOf (gamma (2*(2*L))) g)-
    f (classOf (gamma (2*(2*L))) g)=_
  rw [hh]
  change f (classOf (gamma (2*(2*L))) ((integralLabel (lowerSL (2*L) 0))⁻¹*g))+
    f (classOf (gamma (2*(2*L))) ((integralLabel (lowerSL (2*L) 1))⁻¹*g))-
    f (classOf (gamma (2*(2*L))) g)=_
  rw [hz,map_one,inv_one,one_mul]
  abel

/-- A word identity modulo the level subgroup is an operator identity
on the original counting quotient. -/
theorem pullback_power_apply {N : ℕ} (A : Space N→L[ℂ]Space N) (a : G)
    (hA : ∀ f g,A f (classOf (gamma N) g)=f (classOf (gamma N) (a⁻¹*g)))
    (n : ℕ) (f : Space N) (g : G) :
    (A^n) f (classOf (gamma N) g)=f (classOf (gamma N) ((a^n)⁻¹*g)) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' A n,mul_apply_eq_comp,hA,ih,pow_succ' a n,mul_inv_rev,mul_assoc]

theorem pullback_power_eq_one {N : ℕ} (A : Space N→L[ℂ]Space N) (a : G)
    (hA : ∀ f g,A f (classOf (gamma N) g)=f (classOf (gamma N) (a⁻¹*g)))
    (n : ℕ) (hn : a^n∈gamma N) : A^n=1 := by
  ext f q
  induction q using Quotient.inductionOn with
  | h g =>
    change (A^n) f (classOf (gamma N) g)=f (classOf (gamma N) g)
    rw [pullback_power_apply A a hA n]
    change f (classOf (gamma N) ((a^n)⁻¹*g))=f (classOf (gamma N) g)
    rw [classOf_mul (gamma N) ⟨(a^n)⁻¹,(gamma N).inv_mem hn⟩ g]


theorem repeatedConjugate_apply (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))]
    (f : Space (2*(2*L))) (g : G) :
    repeatedConjugate L hL f (classOf (gamma (2*(2*L))) g)=
      f (classOf (gamma (2*(2*L))) ((translationLabel (-1/2))⁻¹*g)) := by
  let hN : 0<2*(2*L) := by omega
  let W := normalizerOperator (2*(2*L)) (completedFrickeNormalizer (2*(2*L)) hN)
  change repeatedOrdinary L (W f)
    (classOf (gamma (2*(2*L))) (frickeLabel (2*(2*L)) hN*g))=_
  rw [repeatedOrdinary_apply L hL]
  change f (classOf (gamma (2*(2*L)))
    (frickeLabel (2*(2*L)) hN*((integralLabel (lowerSL (2*L) 1))⁻¹*
      (frickeLabel (2*(2*L)) hN*g))))=_
  have hc : frickeLabel (2*(2*L)) hN*integralLabel (lowerSL (2*L) 1)*
      frickeLabel (2*(2*L)) hN=translationLabel (-1/2) := by
    rw [QuantitativeArithmeticRepeatedTwoMatrices.fricke_half L hL,mul_assoc,
      frickeLabel_mul_self,mul_one]
  have hi := congrArg (fun a => a⁻¹) hc
  simp only [mul_inv_rev,frickeLabel_inv] at hi
  have he : frickeLabel (2*(2*L)) hN*((integralLabel (lowerSL (2*L) 1))⁻¹*
      (frickeLabel (2*(2*L)) hN*g))=(translationLabel (-1/2))⁻¹*g := by
    rw [←mul_assoc] at hi
    rw [←mul_assoc,←mul_assoc,hi]
  rw [he]

theorem repeatedOrdinary_square (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    repeatedOrdinary L*repeatedOrdinary L=1 := by
  simpa only [pow_two] using pullback_power_eq_one (repeatedOrdinary L)
    (integralLabel (lowerSL (2*L) 1)) (repeatedOrdinary_apply L hL) 2
    (QuantitativeArithmeticRepeatedTwoMatrices.lower_square L)

theorem repeatedProduct_apply (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))]
    (f : Space (2*(2*L))) (g : G) :
    (repeatedOrdinary L*repeatedConjugate L hL) f (classOf (gamma (2*(2*L))) g)=
      f (classOf (gamma (2*(2*L)))
        ((integralLabel (lowerSL (2*L) 1)*translationLabel (-1/2))⁻¹*g)) := by
  rw [mul_apply_eq_comp,repeatedOrdinary_apply L hL,repeatedConjugate_apply L hL,mul_inv_rev,mul_assoc]

theorem repeatedProduct_even (t : ℕ) (ht : 0<t) [NeZero (2*(2*(2*t)))] :
    (repeatedOrdinary (2*t)*repeatedConjugate (2*t) (by omega))^2=1 :=
  pullback_power_eq_one _ _ (repeatedProduct_apply (2*t) (by omega)) 2
    (QuantitativeArithmeticRepeatedTwoMatrices.even_word t)

theorem repeatedProduct_odd (t : ℕ) [NeZero (2*(2*(2*t+1)))] :
    (repeatedOrdinary (2*t+1)*repeatedConjugate (2*t+1) (by omega))^3=1 :=
  pullback_power_eq_one _ _ (repeatedProduct_apply (2*t+1) (by omega)) 3
    (QuantitativeArithmeticRepeatedTwoMatrices.odd_word t)

#print axioms repeatedConjugate_apply
#print axioms repeatedOrdinary_square
#print axioms repeatedProduct_even
#print axioms repeatedProduct_odd

#print axioms coverTraceOperator_cosets
#print axioms repeatedOrdinary_apply
#print axioms pullback_power_eq_one
end QuantitativeMaass.Counting
