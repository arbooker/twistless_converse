module

public import QuantitativeNewGapTreeArithmeticBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticNestedQuotients
open scoped MatrixGroups BigOperators lp

/-- Membership in the literal second old group, transported by dilation. -/
theorem mem_degeneracy_iff_dilation (M p : ℕ) (hp : 0 < p)
    (g : AsymptoticRationalGroup.Group) :
    g ∈ degeneracyGroup M p hp ↔
      dilationLabel p hp*g*(dilationLabel p hp)⁻¹ ∈ gamma M := by
  constructor
  · rintro ⟨j,hj,he⟩
    change (dilationLabel p hp)⁻¹*j*((dilationLabel p hp)⁻¹)⁻¹=g at he
    change j ∈ gamma M at hj
    rw [← he]
    simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hj
  · intro h
    refine ⟨dilationLabel p hp*g*(dilationLabel p hp)⁻¹,h,?_⟩
    change (dilationLabel p hp)⁻¹*(dilationLabel p hp*g*(dilationLabel p hp)⁻¹)*
      ((dilationLabel p hp)⁻¹)⁻¹=g
    group

/-- Dilation gives a representative-compatible equivalence of the two
actual old quotient sets: K*g is sent to J*(D*g). -/
def dilationCosetEquiv (M p : ℕ) (hp : 0 < p) :
    Classes (degeneracyGroup M p hp) ≃ Classes (gamma M) where
  toFun := Quotient.map (fun g => dilationLabel p hp*g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    have hh := (mem_degeneracy_iff_dilation M p hp _).mp
      (QuotientGroup.rightRel_apply.mp hab)
    simpa only [_root_.mul_inv_rev,mul_assoc] using hh)
  invFun := Quotient.map (fun g => (dilationLabel p hp)⁻¹*g) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    apply (mem_degeneracy_iff_dilation M p hp _).mpr
    have he : dilationLabel p hp*((dilationLabel p hp)⁻¹*b*
        ((dilationLabel p hp)⁻¹*a)⁻¹)*(dilationLabel p hp)⁻¹=b*a⁻¹ := by group
    rw [he]
    exact QuotientGroup.rightRel_apply.mp hab)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf _ ((dilationLabel p hp)⁻¹*(dilationLabel p hp*g))=classOf _ g
      rw [inv_mul_cancel_left]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change classOf _ (dilationLabel p hp*((dilationLabel p hp)⁻¹*g))=classOf _ g
      rw [mul_inv_cancel_left]

@[simp] theorem dilationCosetEquiv_classOf (M p : ℕ) (hp : 0 < p)
    (g : AsymptoticRationalGroup.Group) :
    dilationCosetEquiv M p hp (classOf (degeneracyGroup M p hp) g)=
      classOf (gamma M) (dilationLabel p hp*g) := rfl

/-- Counting measure makes the literal dilation pullback a unitary
between the two quotient Hilbert spaces. -/
def dilationUnitary (M p : ℕ) (hp : 0 < p) :
    ℓ²(Classes (gamma M),ℂ) ≃ₗᵢ[ℂ] ℓ²(Classes (degeneracyGroup M p hp),ℂ) where
  toFun f := ⟨fun q => f (dilationCosetEquiv M p hp q),
    memℓp_gen (((dilationCosetEquiv M p hp).summable_iff).mpr
      ((lp.memℓp f).summable (by norm_num)))⟩
  invFun f := ⟨fun q => f ((dilationCosetEquiv M p hp).symm q),
    memℓp_gen (((dilationCosetEquiv M p hp).symm.summable_iff).mpr
      ((lp.memℓp f).summable (by norm_num)))⟩
  left_inv f := by ext q; simp
  right_inv f := by ext q; simp
  map_add' f g := by ext q; rfl
  map_smul' c f := by ext q; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact (dilationCosetEquiv M p hp).tsum_eq (fun q => ‖f q‖^(2 : ENNReal).toReal)

@[simp] theorem dilationUnitary_apply (M p : ℕ) (hp : 0 < p)
    (f : ℓ²(Classes (gamma M),ℂ)) (g : AsymptoticRationalGroup.Group) :
    dilationUnitary M p hp f (classOf (degeneracyGroup M p hp) g)=
      f (classOf (gamma M) (dilationLabel p hp*g)) := rfl

/-- The normalized regular Hecke operator is the actual cross Gram after
identifying the second old quotient by the dilation unitary. -/
def regularHecke (M p : ℕ) [NeZero M] [Fact p.Prime] :
    ℓ²(Classes (gamma M),ℂ) →L[ℂ] ℓ²(Classes (gamma M),ℂ) :=
  (isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint.comp
    ((isometry (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
      (Fact.out : p.Prime).pos)).toContinuousLinearMap.comp
        (dilationUnitary M p (Fact.out : p.Prime).pos).toLinearIsometry.toContinuousLinearMap)

/-- On every actual congruence coset the operator is the normalized sum
of diag(p,1) and the p matrices [[1,a],[0,p]]. -/
theorem regularHecke_apply (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1)
    (f : ℓ²(Classes (gamma M),ℂ)) (g : AsymptoticRationalGroup.Group) :
    regularHecke M p f (classOf (gamma M) g)=((p+1 : ℕ) : ℂ)⁻¹ *
      (f (classOf (gamma M) (dilationLabel p (Fact.out : p.Prime).pos*g)) +
        ∑ a : Fin p, f (classOf (gamma M)
          (upperHeckeLabel p (Fact.out : p.Prime).pos a.val*g))) := by
  unfold regularHecke
  change ((isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint
    (isometry (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
      (Fact.out : p.Prime).pos) (dilationUnitary M p (Fact.out : p.Prime).pos f))) _ = _
  rw [old_cross_gram_hecke M p hpM A B hAB]
  simp only [dilationUnitary_apply,← mul_assoc,mul_inv_cancel,one_mul]

/-- No choice of Bezout coefficients remains in the concrete formula. -/
theorem regularHecke_apply_prime (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p ∣ M) (f : ℓ²(Classes (gamma M),ℂ))
    (g : AsymptoticRationalGroup.Group) :
    regularHecke M p f (classOf (gamma M) g)=((p+1 : ℕ) : ℂ)⁻¹ *
      (f (classOf (gamma M) (dilationLabel p (Fact.out : p.Prime).pos*g)) +
        ∑ a : Fin p, f (classOf (gamma M)
          (upperHeckeLabel p (Fact.out : p.Prime).pos a.val*g))) := by
  have hc : p.Coprime M := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have hAB : (p : ℤ)*Nat.gcdA p M+(M : ℤ)*Nat.gcdB p M=1 := by
    have hh := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at hh
    exact hh.symm
  exact regularHecke_apply M p hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB f g

/-- Dilation changes neither the old angle nor its operator norm. -/
theorem regularHecke_norm_eq_cross_gram (M p : ℕ) [NeZero M] [Fact p.Prime] :
    ‖regularHecke M p‖ =
      ‖(isometry (gamma_le_of_dvd (Nat.dvd_mul_left M p))).toContinuousLinearMap.adjoint.comp
        (isometry (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
          (Fact.out : p.Prime).pos)).toContinuousLinearMap‖ := by
  unfold regularHecke
  rw [← ContinuousLinearMap.comp_assoc]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _
    (dilationUnitary M p (Fact.out : p.Prime).pos)

#print axioms mem_degeneracy_iff_dilation
#print axioms dilationCosetEquiv
#print axioms dilationUnitary
#print axioms regularHecke_apply
#print axioms regularHecke_apply_prime
#print axioms regularHecke_norm_eq_cross_gram

end QuantitativeNewGap
