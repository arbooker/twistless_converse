module

public import QuantitativeNewGapTreeFaithfulV1
public import AsymptoticClassicalHeckeNormalizerV1
public import QuantitativeMaassTreeOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticClassicalCusp AsymptoticAtkinLehner QuantitativeMaass
open AsymptoticQuotientOperators AsymptoticPermutationInvariant
open scoped lp

/-- The concrete determinant-p normalizer is an involution on level-pM
cosets, because its square belongs to that exact congruence group. -/
def heckeSwapEquiv (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) : Classes (gamma (p*M)) ≃ Classes (gamma (p*M)) := by
  let W := heckeNormalizerLabel M p hp A B hAB
  have hW : W*W ∈ gamma (p*M) := by
    dsimp only [W]
    rw [heckeNormalizerLabel_eq M p hp A B hAB hM]
    rw [← _root_.mul_inv_rev]
    exact (gamma (p*M)).inv_mem (localAtkin_square_mem M p hM hp A B hAB)
  let e : Classes (gamma (p*M)) → Classes (gamma (p*M)) :=
    Quotient.map (fun g => W*g) (by
      intro a b hab
      apply QuotientGroup.rightRel_apply.mpr
      have hh := heckeNormalizer_conj_mem M p hp A B hAB hM
        (QuotientGroup.rightRel_apply.mp hab)
      simpa only [_root_.mul_inv_rev,mul_assoc] using hh)
  have hi : Function.Involutive e := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf (gamma (p*M)) (W*(W*g))=classOf (gamma (p*M)) g
      rw [← mul_assoc]
      exact classOf_mul _ ⟨W*W,hW⟩ g
  exact ⟨e,e,hi,hi⟩

theorem heckeSwapEquiv_classOf (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) (g : AsymptoticRationalGroup.Group) :
    heckeSwapEquiv M p hM hp A B hAB (classOf (gamma (p*M)) g)=
      classOf (gamma (p*M)) (heckeNormalizerLabel M p hp A B hAB*g) := rfl

def heckeSwap (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) :
    ℓ²(Classes (gamma (p*M)),ℂ) →L[ℂ] ℓ²(Classes (gamma (p*M)),ℂ) :=
  (l2Permutation (heckeSwapEquiv M p hM hp A B hAB)).toContinuousLinearEquiv.toContinuousLinearMap

theorem heckeSwap_selfAdjoint (M p : ℕ) (hM : 0 < M) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) : IsSelfAdjoint (heckeSwap M p hM hp A B hAB) := by
  change (heckeSwap M p hM hp A B hAB).adjoint = _
  rw [heckeSwap,LinearIsometryEquiv.adjoint_eq_symm]
  ext f q
  rfl

/-- The actual Hecke correspondence is a compression of the concrete
selfadjoint normalizer permutation of the raised-level cosets. -/
theorem regularHecke_eq_compression (M p : ℕ) [NeZero M] [Fact p.Prime]
    (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1) :
    regularHecke M p =
      (isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint.comp
        ((heckeSwap M p (Nat.pos_of_ne_zero (NeZero.ne M)) (Fact.out : p.Prime).pos A B hAB).comp
          (isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap) := by
  unfold regularHecke
  congr 1
  ext f q
  induction q using Quotient.inductionOn with
  | h g =>
    change isometry _ (dilationUnitary M p (Fact.out : p.Prime).pos f) (classOf (gamma (p*M)) g) =
      isometry _ f (classOf (gamma (p*M)) (heckeNormalizerLabel M p (Fact.out : p.Prime).pos A B hAB*g))
    rw [isometry_apply,isometry_apply,forget_classOf,forget_classOf,dilationUnitary_apply]
    have hi : ((gamma (p*M)).subgroupOf (degeneracyGroup M p (Fact.out : p.Prime).pos)).index =
        ((gamma (p*M)).subgroupOf (gamma M)).index :=
      degeneracyGroup_index M p (Nat.pos_of_ne_zero (NeZero.ne M)) (Fact.out : p.Prime).pos
    rw [hi]
    congr 1
    apply congrArg f
    change classOf (gamma M) (dilationLabel p _*g) =
      classOf (gamma M) ((integralLabel (heckeSL M p A B hAB)⁻¹*dilationLabel p _)*g)
    rw [mul_assoc]
    symm
    have hj : integralLabel (heckeSL M p A B hAB)⁻¹ ∈ gamma M :=
      ⟨_,(CongruenceSubgroup.Gamma0 M).inv_mem (heckeSL_mem M p A B hAB),rfl⟩
    exact classOf_mul (gamma M) ⟨_,hj⟩ _

theorem old_compression_selfAdjoint {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (I : E →L[ℂ] F) (V : F →L[ℂ] F)
    (hV : IsSelfAdjoint V) : IsSelfAdjoint (I.adjoint.comp (V.comp I)) := by
  change (I.adjoint.comp (V.comp I)).adjoint = I.adjoint.comp (V.comp I)
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  have hV' : V.adjoint=V := hV
  rw [hV',ContinuousLinearMap.comp_assoc]

/-- Selfadjointness of the literal good-prime regular Hecke operator. -/
theorem regularHecke_selfAdjoint (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) : IsSelfAdjoint (regularHecke M p) := by
  have hc : p.Coprime M := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have hAB : (p : ℤ)*Nat.gcdA p M+(M : ℤ)*Nat.gcdB p M=1 := by
    have hh := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at hh
    exact hh.symm
  rw [regularHecke_eq_compression M p (Nat.gcdA p M) (Nat.gcdB p M) hAB]
  exact old_compression_selfAdjoint _ _ (heckeSwap_selfAdjoint M p
    (Nat.pos_of_ne_zero (NeZero.ne M)) (Fact.out : p.Prime).pos
      (Nat.gcdA p M) (Nat.gcdB p M) hAB)

/-- Continuous real spectral functions retain the proved arithmetic
translation symmetry, so quotient-root faithfulness applies to them. -/
theorem regularHecke_cfc_equivariant (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) (f : ℝ → ℝ) (hf : Continuous f) :
    Equivariant (AsymptoticFunctionalCalculus.value f (regularHecke M p)) :=
  fun a => invariant_cfc _ _ (regularHecke_equivariant M p hpM a)
    (regularHecke_selfAdjoint M p hpM) f hf

#print axioms heckeSwap_selfAdjoint
#print axioms regularHecke_eq_compression
#print axioms regularHecke_selfAdjoint
#print axioms regularHecke_cfc_equivariant

end QuantitativeNewGap
