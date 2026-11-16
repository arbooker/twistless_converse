module

public import QuantitativeMaassCountingRepeatedTraceV1
public import QuantitativeMaassCountingGramExpressionV1
public import QuantitativeMaassCountingOldPairV1
public import QuantitativeArithmeticRepeatedTwoProjectorV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap Polynomial AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticNestedQuotients AsymptoticQuotientOperators QuantitativeNewGap
open QuantitativeArithmeticRepeatedTwoProjector AsymptoticFreshMatrices AsymptoticIntegralSubgroup
namespace QuantitativeMaass.Counting

theorem repeatedFricke_square (L : ℕ) (hL : 0<L) :
    let W := normalizerOperator (2*(2*L)) (completedFrickeNormalizer (2*(2*L)) (by omega))
    W*W=1 := by
  intro W
  ext f q
  induction q using Quotient.inductionOn with
  | h g =>
    change f (classOf (gamma (2*(2*L)))
      (frickeLabel (2*(2*L)) (by omega)*(frickeLabel (2*(2*L)) (by omega)*g)))=
        f (classOf (gamma (2*(2*L))) g)
    rw [←mul_assoc (frickeLabel (2*(2*L)) (by omega))
      (frickeLabel (2*(2*L)) (by omega)) g,frickeLabel_mul_self,one_mul]

theorem repeatedConjugate_square (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    repeatedConjugate L hL*repeatedConjugate L hL=1 := by
  let W := normalizerOperator (2*(2*L)) (completedFrickeNormalizer (2*(2*L)) (by omega))
  let B := repeatedOrdinary L
  have hW : W*W=1 := repeatedFricke_square L hL
  have hB : B*B=1 := repeatedOrdinary_square L hL
  have hww (x : Space (2*(2*L))→L[ℂ]Space (2*(2*L))) : W*(W*x)=x := by
    rw [←mul_assoc W W x,hW,one_mul]
  have hbb (x : Space (2*(2*L))→L[ℂ]Space (2*(2*L))) : B*(B*x)=x := by
    rw [←mul_assoc B B x,hB,one_mul]
  change (W*(B*W))*(W*(B*W))=1
  simp only [mul_assoc,hww,hbb,hW]

def repeatedSum (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    Space (2*(2*L))→L[ℂ]Space (2*(2*L)) := repeatedOrdinary L+repeatedConjugate L hL

theorem repeatedSum_even_cubic (t : ℕ) (ht : 0<t) [NeZero (2*(2*(2*t)))] :
    (repeatedSum (2*t) (by omega))^3-4*repeatedSum (2*t) (by omega)=0 :=
  square_product_cubic _ _ (repeatedOrdinary_square (2*t) (by omega))
    (repeatedConjugate_square (2*t) (by omega)) (repeatedProduct_even t ht)

theorem repeatedSum_odd_quartic (t : ℕ) [NeZero (2*(2*(2*t+1)))] :
    (repeatedSum (2*t+1) (by omega))^4-5*(repeatedSum (2*t+1) (by omega))^2+4=0 :=
  QuantitativeArithmeticTwoInvolutionPolynomial.cube_product _ _
    (repeatedOrdinary_square (2*t+1) (by omega))
    (repeatedConjugate_square (2*t+1) (by omega)) (repeatedProduct_odd t)

theorem repeatedSum_annihilator (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    aeval (repeatedSum L hL) annihilator=0 := by
  rcases Nat.even_or_odd L with he | ho
  · obtain ⟨t,he⟩ := he
    rw [←two_mul] at he
    subst L
    have ht : 0<t := by omega
    have hp : annihilator=(X^2-1)*(X^3-4*X) := by unfold annihilator; ring
    rw [hp,map_mul]
    have hc : aeval (repeatedSum (2*t) hL) (X^3-4*X : ℂ[X])=0 := by
      simpa only [map_sub,map_mul,map_pow,Polynomial.aeval_X,map_ofNat] using repeatedSum_even_cubic t ht
    rw [hc,mul_zero]
  · obtain ⟨t,rfl⟩ := ho
    have hp : annihilator=X*(X^4-5*X^2+4) := by unfold annihilator; ring
    rw [hp,map_mul]
    have hc : aeval (repeatedSum (2*t+1) hL) (X^4-5*X^2+4 : ℂ[X])=0 := by
      simpa only [map_sub,map_add,map_mul,map_pow,Polynomial.aeval_X,map_ofNat] using repeatedSum_odd_quartic t
    rw [hc,mul_zero]

theorem repeatedSum_selfAdjoint (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    IsSelfAdjoint (repeatedSum L hL) := by
  have hI : IsSelfAdjoint (1 : Space (2*(2*L))→L[ℂ]Space (2*(2*L))) := by
    change (1 : _→L[ℂ]_).adjoint=1
    exact ContinuousLinearMap.adjoint_one
  have hB : IsSelfAdjoint (repeatedOrdinary L) := by
    unfold repeatedOrdinary
    apply clm_selfAdjoint_sub
    · exact coverTraceOperator_selfAdjoint (Nat.dvd_mul_left (2*L) 2)
    · exact hI
  exact hB.add (ambient_conjugate_selfAdjoint _ _ hB
    (frickeOperator_selfAdjoint (2*(2*L)) (by omega)))

/-- The exact repeated-two polynomial on the counting space, with its
range proved from the finite group word identities. -/
theorem repeatedTwoNewFilter_projection (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    repeatedTwoNewFilter (by omega : 0<2*(2*L)) (Nat.dvd_mul_left (2*L) 2)=
      (repeatedSum L hL+2).ker.starProjection := by
  have hh := projector_eq_starProjection (repeatedSum L hL)
    (repeatedSum_selfAdjoint L hL) (repeatedSum_annihilator L hL)
  rw [projector_formula] at hh
  exact hh


theorem repeatedSum_add_two (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    repeatedSum L hL+2=oldPair (by omega : 0<2*(2*L)) (Nat.dvd_mul_left (2*L) 2) :=
  sum_two_reflections (coverTraceOperator (Nat.dvd_mul_left (2*L) 2))
    (normalizerOperator (2*(2*L)) (completedFrickeNormalizer (2*(2*L)) (by omega)))
    (repeatedFricke_square L hL)

theorem repeatedSum_kernel (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    (repeatedSum L hL+2).ker=
      newSpace (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))
        (gamma_le_frickeOldGroup (by omega : 0<2*(2*L)) (Nat.dvd_mul_left (2*L) 2)) := by
  rw [repeatedSum_add_two,oldPair_projection_formula,newSpace_eq_old_sum_kernel]
  have hn : (((gamma (2*(2*L))).subgroupOf (gamma (2*L))).index:ℂ)≠0 := by
    exact_mod_cast (index_pos (H:=gamma (2*(2*L))) (J:=gamma (2*L))).ne'
  ext x
  change (((gamma (2*(2*L))).subgroupOf (gamma (2*L))).index:ℂ) •
    (((space (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))).starProjection+
      (space (gamma_le_frickeOldGroup (by omega : 0<2*(2*L))
        (Nat.dvd_mul_left (2*L) 2))).starProjection) x)=0 ↔ _
  simp only [smul_eq_zero,hn,false_or]
  rfl

/-- The repeated-two polynomial is the actual local-new projection,
not merely a projection onto an unnamed polynomial kernel. -/
theorem repeatedTwoNewFilter_newSpace (L : ℕ) (hL : 0<L) [NeZero (2*(2*L))] :
    repeatedTwoNewFilter (by omega : 0<2*(2*L)) (Nat.dvd_mul_left (2*L) 2)=
      (newSpace (gamma_le_of_dvd (Nat.dvd_mul_left (2*L) 2))
        (gamma_le_frickeOldGroup (by omega : 0<2*(2*L)) (Nat.dvd_mul_left (2*L) 2))).starProjection := by
  rw [repeatedTwoNewFilter_projection L hL]
  exact AsymptoticPolarIsometry.starProjection_congr _ _ (repeatedSum_kernel L hL)

#print axioms repeatedSum_kernel
#print axioms repeatedTwoNewFilter_newSpace

#print axioms repeatedFricke_square
#print axioms repeatedConjugate_square
#print axioms repeatedSum_annihilator
#print axioms repeatedTwoNewFilter_projection
end QuantitativeMaass.Counting
