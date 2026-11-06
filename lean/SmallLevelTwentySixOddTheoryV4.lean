module

public import FinitenessFiniteOrderClosureV1
public import Mathlib.Tactic.Group
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import QuantitativeArithmeticQuadraticTwistQuotientOrderV1
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelCrossedFrickeV1
public import SmallLevelMellinUnscaleV1
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelRamifiedTwoAdditiveV1
public import SmallLevelSimplePoleTaylorTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelThreePairV1
public import SmallLevelTwentySixGridParametersV1
public import SmallLevelTwentySixGroupTheoryV4
public import SmallLevelTwentySixQuarterTheoryV4
public import SmallLevelTwentySixTwelfthMellinV1

/-! Consolidated chapter: SmallLevelTwentySixOdd. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixOddHeckeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Complex SmallLevelAdditive SmallLevelTaylor
open SmallLevelRamifiedTwoAdditive (heckeScalar)

def odd (k : ℕ) (f : ℕ→ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  original k f (1/(q:ℝ)) s-original k f (-1/(q:ℝ)) s

def thirdFactor (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  heckeScalar m f s+(heckeScalar m f s)^2

def quarterFactor (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  1+((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)+((3:ℂ)^((m:ℂ)-s))^2

/-- Exact odd Hecke relation from the original ramified-two and good-three
Euler rows. No eigenvalue is divided out. -/
theorem original_odd_hecke (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      2*odd (2*m) f 12 s=thirdFactor m f s*odd (2*m) f 3 s+
        quarterFactor m f s*odd (2*m) f 4 s := by
  obtain ⟨B2,h2⟩:=SmallLevelRamifiedTwoAdditive.original_ramified_row (by decide : 2∣26) m hm hf
  obtain ⟨B3,h3⟩:=normalized_additive_hecke hf (by decide : Nat.Prime 3) (by decide : ¬3∣26)
  refine ⟨max B2 B3,fun s hs => ?_⟩
  have hs2:=lt_of_le_of_lt (le_max_left B2 B3) hs
  have hs3:=lt_of_le_of_lt (le_max_right B2 B3) hs
  have h21:=h2 (1/12) s hs2
  have h2n1:=h2 (-1/12) s hs2
  have h22:=h2 (1/6) s hs2
  have h2n2:=h2 (-1/6) s hs2
  have h31:=h3 (1/12) s hs3
  have h3n1:=h3 (-1/12) s hs3
  norm_num [Finset.sum_range_succ] at h21 h2n1 h22 h2n2 h31 h3n1
  have hp (r : ℝ) (n : ℤ) : original (2*m) f (r+(n:ℝ)) s=original (2*m) f r s :=
    transform_add_int _ r n s
  have h23 : original (2*m) f (2/3) s=original (2*m) f (-1/3) s := by
    convert hp (-1/3) 1 using 1; norm_num
  have h34 : original (2*m) f (3/4) s=original (2*m) f (-1/4) s := by
    convert hp (-1/4) 1 using 1; norm_num
  have hn34 : original (2*m) f (-3/4) s=original (2*m) f (1/4) s := by
    convert hp (1/4) (-1) using 1; norm_num
  simp only [neg_div] at h23 h34 hn34
  rw [h23] at h22
  rw [h34] at h31
  rw [hn34] at h3n1
  unfold odd thirdFactor quarterFactor
  norm_num only [Nat.cast_ofNat,neg_div]
  linear_combination h31-h3n1+h21-h2n1+(heckeScalar m f s)*(h22-h2n2)

#print axioms original_odd_hecke
end SmallLevelTwentySixOdd
end
end

/-! ## SmallLevelTwentySixThirdContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Complex SmallLevelAdditive SmallLevelNormalized Filter Set
open SmallLevelRamifiedTwoAdditive (heckeScalar)
open SmallLevelTwentySixQuarter (quarterEntire original_quarter_continuation)
open SmallLevelTwentySixTwelfth (twelfthEntire original_twelfth_continuation)
open SmallLevelTwentySix (P)
open scoped Topology MatrixGroups ModularForm

def thirdNumerator (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  2*twelfthEntire m f s-quarterFactor m f s*quarterEntire m f s

theorem thirdFactor_entire (m : ℕ) (f : ℕ→ℂ) : Differentiable ℂ (thirdFactor m f) := by
  unfold thirdFactor heckeScalar
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop

theorem quarterFactor_entire (m : ℕ) (f : ℕ→ℂ) : Differentiable ℂ (quarterFactor m f) := by
  unfold quarterFactor
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop

theorem thirdFactor_nonzero (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 26 f) : ∃ s : ℂ,thirdFactor m f s≠0 := by
  have hu : QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2≠0 := by
    rcases QuantitativeArithmeticRamifiedFullTrace.multiplier_simple hf
      (by decide : Nat.Prime 2) (by decide : 2∣26) (by decide : ¬2^2∣26) m with h|h
    · rw [h]; exact pow_ne_zero _ (by norm_num)
    · rw [h]; exact neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  by_contra h
  push Not at h
  have h0:=h 0
  have h1:=h 1
  norm_num [thirdFactor,heckeScalar,Complex.cpow_neg] at h0 h1
  apply hu
  linear_combination 4*h1-h0

theorem thirdNumerator_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
    Differentiable ℂ (thirdNumerator m f) := by
  exact ((original_twelfth_continuation m hm hf η hη hW).1.const_mul 2).sub
    ((quarterFactor_entire m f).mul (original_quarter_continuation m hm hf η hη hW hP).1)

theorem original_third_product (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → thirdNumerator m f s=thirdFactor m f s*odd (2*m) f 3 s := by
  obtain ⟨Bq,hq⟩:=(original_quarter_continuation m hm hf η hη hW hP).2
  obtain ⟨Bt,ht⟩:=(original_twelfth_continuation m hm hf η hη hW).2
  obtain ⟨Bh,hh⟩:=original_odd_hecke m hm hf
  refine ⟨max Bq (max Bt Bh),fun s hs => ?_⟩
  have hsq:=lt_of_le_of_lt (le_max_left Bq (max Bt Bh)) hs
  have hst:=lt_of_le_of_lt ((le_max_left Bt Bh).trans (le_max_right Bq _)) hs
  have hsh:=lt_of_le_of_lt ((le_max_right Bt Bh).trans (le_max_right Bq _)) hs
  unfold thirdNumerator
  rw [hq s hsq,ht s hst]
  have he:=hh s hsh
  unfold odd at he ⊢
  norm_num only [Nat.cast_ofNat,neg_div] at he ⊢
  linear_combination he

/-- Conditional only on the remaining P transformation, the odd third
combination continues meromorphically. Poles on the scalar denominator
are retained; this theorem is not an entireness or modularity claim. -/
theorem third_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ→ℂ), (∀ s,MeromorphicNFAt G s) ∧
      (∀ s,bound<s.re → G s=odd (2*m) f 3 s) ∧
      (∀ s,thirdFactor m f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x,G=ᶠ[𝓝[≠] x] (fun s => thirdNumerator m f s/thirdFactor m f s)) := by
  obtain ⟨B,hB⟩:=original_common_halfplane hf
  obtain ⟨C,hC⟩:=original_third_product m hm hf η hη hW hP
  obtain ⟨G,hG,hagree,hpole,hgerm⟩:=QuantitativeArithmeticEntireQuotient.continuation
    (thirdNumerator m f) (thirdFactor m f) (odd (2*m) f 3) (max B C)
    (fun z => (thirdNumerator_entire m hm hf η hη hW hP).analyticAt z)
    (fun z => (thirdFactor_entire m f).analyticAt z) (thirdFactor_nonzero m hf.toEulerData)
    (fun z hz => ((hB (1/3) z ((le_max_left _ _).trans_lt hz)).1).sub
      (hB (-1/3) z ((le_max_left _ _).trans_lt hz)).1)
    (fun z hz => hC z ((le_max_right _ _).trans_lt hz))
  exact ⟨max B C,G,hG,hagree,hpole,hgerm⟩

/-- At weights divisible by four, the continuation follows from original
input alone. Its possible denominator poles still need exclusion. -/
theorem even_half_weight_continuation (m : ℕ) (hm : 0<m) (heven : Even m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ→ℂ), (∀ s,MeromorphicNFAt G s) ∧
      (∀ s,bound<s.re → G s=odd (2*m) f 3 s) ∧
      (∀ s,thirdFactor m f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x,G=ᶠ[𝓝[≠] x] (fun s => thirdNumerator m f s/thirdFactor m f s)) := by
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<26) m hf
  exact third_continuation m hm hf η hη hW (SmallLevelTwentySix.original_P_even_half_weight m hm heven hf)

#print axioms third_continuation
#print axioms even_half_weight_continuation
end SmallLevelTwentySixOdd
end
end

/-! ## SmallLevelTwentySixThirdFiniteOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Complex Filter SmallLevelAdditive SmallLevelNormalized
open SmallLevelTwentySixGrid (badParameter badParameter_two_sign)
open SmallLevelRamifiedTwoAdditive (heckeScalar)
open SmallLevelTwentySixQuarter (quarterEntire original_quarter_entire)
open SmallLevelTwentySixTwelfth (twelfthEntire original_twelfth_entire)
open SmallLevelTwentySix (P)
open scoped Topology MatrixGroups ModularForm

theorem centered_power_bound {r : ℝ} (hr : 0<r) (m : ℕ) :
    FinitenessFiniteOrder.Bound (fun s : ℂ => (r:ℂ)^((m:ℂ)-s)) := by
  have he : (fun s : ℂ => (r:ℂ)^((m:ℂ)-s))=
      (fun s : ℂ => (r:ℂ)^m*(r:ℂ)^(-s)) := by
    funext s
    rw [sub_eq_add_neg,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne'),
      Complex.cpow_natCast]
  rw [he]
  exact FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
    (SmallLevelMellinUnscale.negative_cpow_bound hr)

theorem quarterFactor_bound (m : ℕ) (f : ℕ→ℂ) :
    FinitenessFiniteOrder.Bound (quarterFactor m f) := by
  exact FinitenessFiniteOrderClosure.add
    (FinitenessFiniteOrderClosure.add (FinitenessInputBounds.bound_const 1)
      (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
        (centered_power_bound (by norm_num : (0:ℝ)<3) m)))
    (FinitenessFiniteOrderClosure.pow (centered_power_bound (by norm_num : (0:ℝ)<3) m) 2)

theorem thirdNumerator_bound (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
    FinitenessFiniteOrder.Bound (thirdNumerator m f) := by
  exact FinitenessFiniteOrderClosure.sub
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const 2)
      (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<1872) _
        (original_twelfth_entire m hm hf η hη hW).2.1))
    (FinitenessFiniteOrder.mul (quarterFactor_bound m f)
      (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<208) _
        (original_quarter_entire m hm hf η hη hW hP).2.1))

theorem heckeScalar_centered (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    heckeScalar m f s=badParameter f 2*(2:ℂ)^((m:ℂ)-s) := by
  rw [sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),
    Complex.cpow_natCast]
  unfold heckeScalar QuantitativeArithmeticRamifiedFullTrace.multiplier badParameter
  ring

def inverseTwoScalar (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  badParameter f 2*(2:ℂ)^(s-(m:ℂ))

theorem inverseTwoScalar_product (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 26 f) (s : ℂ) :
    inverseTwoScalar m f s*heckeScalar m f s=1 := by
  have hs : badParameter f 2*badParameter f 2=1 := by
    rcases badParameter_two_sign hf with h|h <;> simp [h]
  have hp : (2:ℂ)^(s-(m:ℂ))*(2:ℂ)^((m:ℂ)-s)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    rw [show s-(m:ℂ)+((m:ℂ)-s)=0 by ring,Complex.cpow_zero]
  rw [inverseTwoScalar,heckeScalar_centered]
  calc
    _=(badParameter f 2*badParameter f 2)*
        ((2:ℂ)^(s-(m:ℂ))*(2:ℂ)^((m:ℂ)-s)) := by ring
    _=1 := by rw [hs,hp,one_mul]

theorem inverseTwoScalar_bound (m : ℕ) (f : ℕ→ℂ) :
    FinitenessFiniteOrder.Bound (inverseTwoScalar m f) := by
  have he : inverseTwoScalar m f=(fun s : ℂ =>
      (badParameter f 2*(2:ℂ)^(-(m:ℂ)))*exp ((Real.log 2:ℂ)*s)) := by
    funext s
    rw [inverseTwoScalar,sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
      show log (2:ℂ)=(Real.log 2:ℂ) from (ofReal_log (by norm_num : (0:ℝ)≤2)).symm]
    ring
  rw [he]
  exact FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
    (FinitenessFiniteOrder.exp_linear (Real.log 2))

/-- The continued odd-third function satisfies the actual Hecke product
identity everywhere once its poles have been removed. -/
theorem third_product_identity (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s,B<s.re → G s=odd (2*m) f 3 s) :
    ∀ s,thirdFactor m f s*G s=thirdNumerator m f s := by
  obtain ⟨C,hC⟩:=original_third_product m hm hf η hη hW hP
  have hleft:=(thirdFactor_entire m f).mul hG
  have hright:=thirdNumerator_entire m hm hf η hη hW hP
  intro s
  have he : (fun z => thirdFactor m f z*G z)=ᶠ[𝓝[≠] s] thirdNumerator m f := by
    apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max B C)
    · exact fun z _ => (hleft.analyticAt z).meromorphicAt
    · exact fun z _ => (hright.analyticAt z).meromorphicAt
    · intro z hz
      dsimp only
      rw [hGF z ((le_max_left _ _).trans_lt hz)]
      exact (hC z ((le_max_right _ _).trans_lt hz)).symm
    · linarith
  exact (((hleft.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hright.analyticAt s).meromorphicNFAt).mp he).eq_of_nhds

/-- No finite-order hypothesis is added to the original solution: it is
inherited through the exact Hecke identity. Entireness and P remain separate
obligations in this intermediate analytic lemma. -/
theorem third_finiteOrder (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s,B<s.re → G s=odd (2*m) f 3 s) :
    FinitenessOriginalInput.FiniteOrder G := by
  have hN:=thirdNumerator_entire m hm hf η hη hW hP
  have hI : Differentiable ℂ (inverseTwoScalar m f) := by
    unfold inverseTwoScalar
    simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
    fun_prop
  apply QuantitativeArithmeticQuadraticTwistQuotient.finiteOrder_of_two_factor
    (badParameter f 2) (m:ℂ) (hI.mul hN).continuous
    (FinitenessInputBounds.bound_finiteOrder (FinitenessFiniteOrder.mul
      (inverseTwoScalar_bound m f) (thirdNumerator_bound m hm hf η hη hW hP))) hG
  intro s
  have he:=third_product_identity m hm hf η hη hW hP hG B hGF s
  have hp:=inverseTwoScalar_product m hf.toEulerData s
  rw [←heckeScalar_centered]
  simp only [Pi.mul_apply]
  rw [←he,thirdFactor]
  linear_combination -(1+heckeScalar m f s)*G s*hp

#print axioms thirdNumerator_bound
#print axioms inverseTwoScalar_product
#print axioms third_product_identity
#print axioms third_finiteOrder
end SmallLevelTwentySixOdd
end
end

/-! ## SmallLevelTwentySixThirdReflectionFactorsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Complex SmallLevelRamifiedTwoAdditive

theorem heckeScalar_reflection_product (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 26 f) (s : ℂ) :
    heckeScalar m f s*heckeScalar m f (((2*m:ℕ):ℂ)-s)=1 := by
  have he : heckeScalar m f (((2*m:ℕ):ℂ)-s)=inverseTwoScalar m f s := by
    rw [heckeScalar_centered,inverseTwoScalar]
    congr 2
    push_cast
    ring
  rw [he,mul_comm]
  exact inverseTwoScalar_product m hf s

/-- The third denominator transforms by the cube of the ramified-two
scalar, including at every zero of the denominator. -/
theorem thirdFactor_reflection (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 26 f) (s : ℂ) :
    thirdFactor m f s=(heckeScalar m f s)^3*
      thirdFactor m f (((2*m:ℕ):ℂ)-s) := by
  have hp:=heckeScalar_reflection_product m hf s
  unfold thirdFactor
  linear_combination -((heckeScalar m f s)^2+
    (heckeScalar m f s)^2*heckeScalar m f (((2*m:ℕ):ℂ)-s)+heckeScalar m f s)*hp

theorem quarterFactor_reflection (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    quarterFactor m f s=((3:ℂ)^((m:ℂ)-s))^2*
      quarterFactor m f (((2*m:ℕ):ℂ)-s) := by
  have hp : (3:ℂ)^((m:ℂ)-s)*(3:ℂ)^((m:ℂ)-(((2*m:ℕ):ℂ)-s))=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
    rw [show (m:ℂ)-s+((m:ℂ)-(((2*m:ℕ):ℂ)-s))=0 by push_cast; ring,
      Complex.cpow_zero]
  unfold quarterFactor
  linear_combination -((3:ℂ)^((m:ℂ)-s)*(3:ℂ)^((m:ℂ)-(((2*m:ℕ):ℂ)-s))+1+
    ((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s))*hp

theorem sqrt_conductor_power {r : ℝ} (hr : 0<r) (m : ℕ) (s : ℂ) :
    (Real.sqrt r:ℂ)^(((2*m:ℕ):ℂ)-2*s)=(r:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hs : (Real.sqrt r:ℂ)*(Real.sqrt r:ℂ)=(r:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hr.le
  have hp:=Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg r) ((m:ℂ)-s)
  rw [hs] at hp
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,←hp]

#print axioms thirdFactor_reflection
#print axioms quarterFactor_reflection
#print axioms sqrt_conductor_power
end SmallLevelTwentySixOdd
end
end

/-! ## SmallLevelTwentySixThirdReflectionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Complex SmallLevelAdditive SmallLevelNormalized FinitenessOriginalFourier
open SmallLevelTwentySixGrid (badParameter badParameter_two_sign root_two)
open SmallLevelRamifiedTwoAdditive (heckeScalar)
open SmallLevelTwentySixQuarter (quarterEntire original_quarter_entire quarterCoefficients)
open SmallLevelTwentySixTwelfth (twelfthEntire original_twelfth_entire)
open SmallLevelTwentySix (P)
open scoped Topology MatrixGroups ModularForm

def thirdReflectionMultiplier (m : ℕ) (η s : ℂ) : ℂ :=
  (η/I^(2*m))*(234:ℂ)^((m:ℂ)-s)

theorem two_cube_conductor (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 26 f) (s : ℂ) :
    (heckeScalar m f s)^3*(234:ℂ)^((m:ℂ)-s)=
      badParameter f 2*(1872:ℂ)^((m:ℂ)-s) := by
  have hs : (badParameter f 2)^3=badParameter f 2 := by
    rcases badParameter_two_sign hf with h|h <;> norm_num [h]
  have hp : ((2:ℂ)^((m:ℂ)-s))^3=(8:ℂ)^((m:ℂ)-s) := by
    rw [←Complex.cpow_nat_mul]
    simpa only [Nat.cast_ofNat,show (2:ℂ)^3=8 by norm_num] using
      Complex.natCast_cpow_natCast_mul 2 3 ((m:ℂ)-s)
  have hc:=Complex.natCast_mul_natCast_cpow 8 234 ((m:ℂ)-s)
  norm_num only [show (8:ℂ)*234=1872 by norm_num] at hc
  rw [heckeScalar_centered,mul_pow,hs,hp,mul_assoc,←hc]

theorem three_square_conductor (m : ℕ) (s : ℂ) :
    ((3:ℂ)^((m:ℂ)-s))^2*(208:ℂ)^((m:ℂ)-s)=(1872:ℂ)^((m:ℂ)-s) := by
  have hp : ((3:ℂ)^((m:ℂ)-s))^2=(9:ℂ)^((m:ℂ)-s) := by
    rw [←Complex.cpow_nat_mul]
    simpa only [Nat.cast_ofNat,show (3:ℂ)^2=9 by norm_num] using
      Complex.natCast_cpow_natCast_mul 3 2 ((m:ℂ)-s)
  have hc:=Complex.natCast_mul_natCast_cpow 9 208 ((m:ℂ)-s)
  norm_num only [show (9:ℂ)*208=1872 by norm_num] at hc
  rw [hp,←hc]

theorem thirdNumerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f)
    (s : ℂ) :
    thirdNumerator m f s=(heckeScalar m f s)^3*thirdReflectionMultiplier m η s*
      thirdNumerator m f (((2*m:ℕ):ℂ)-s) := by
  let χ : ℂ:= -(FinitenessNormalizedTwistProduct.root 26 f 2*η)/I^(2*m)
  have ht:=QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<1872)
    (SmallLevelTwentyEightTwelfth.twelfthCoefficients (fullCoefficients f (2*m))) χ
    (original_twelfth_entire m hm hf η hη hW).2.2 s
  have hq:=QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<208)
    (quarterCoefficients (fullCoefficients f (2*m))) χ
    (original_quarter_entire m hm hf η hη hW hP).2.2 s
  change twelfthEntire m f s=χ*(Real.sqrt 1872:ℂ)^(((2*m:ℕ):ℂ)-2*s)*
    twelfthEntire m f (((2*m:ℕ):ℂ)-s) at ht
  change quarterEntire m f s=χ*(Real.sqrt 208:ℂ)^(((2*m:ℕ):ℂ)-2*s)*
    quarterEntire m f (((2*m:ℕ):ℂ)-s) at hq
  rw [sqrt_conductor_power (by norm_num : (0:ℝ)<1872)] at ht
  rw [sqrt_conductor_power (by norm_num : (0:ℝ)<208)] at hq
  norm_num only [Nat.cast_ofNat,Complex.ofReal_ofNat] at ht hq
  have hqc : quarterFactor m f s*(208:ℂ)^((m:ℂ)-s)=
      (1872:ℂ)^((m:ℂ)-s)*quarterFactor m f (((2*m:ℕ):ℂ)-s) := by
    rw [quarterFactor_reflection]
    calc
      _=(((3:ℂ)^((m:ℂ)-s))^2*(208:ℂ)^((m:ℂ)-s))*
        quarterFactor m f (((2*m:ℕ):ℂ)-s) := by ring
      _=_ := by rw [three_square_conductor]
  have hχ : χ=badParameter f 2*(η/I^(2*m)) := by
    dsimp [χ]
    rw [root_two]
    ring
  have hr : (heckeScalar m f s)^3*thirdReflectionMultiplier m η s=
      χ*(1872:ℂ)^((m:ℂ)-s) := by
    rw [thirdReflectionMultiplier,hχ]
    calc
      _=(η/I^(2*m))*((heckeScalar m f s)^3*(234:ℂ)^((m:ℂ)-s)) := by ring
      _=_ := by rw [two_cube_conductor m hf.toEulerData]; ring
  rw [hr]
  calc
    thirdNumerator m f s=χ*(2*(1872:ℂ)^((m:ℂ)-s)*twelfthEntire m f (((2*m:ℕ):ℂ)-s)-
      (quarterFactor m f s*(208:ℂ)^((m:ℂ)-s))*quarterEntire m f (((2*m:ℕ):ℂ)-s)) := by
        rw [thirdNumerator,ht,hq]
        ring
    _=_ := by rw [hqc,thirdNumerator]; ring

/-- Exact meromorphic reflection from the original quarter and twelfth
Mellin laws. Pole removal remains a separate obligation. -/
theorem third_reflection (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 26 (by decide)=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∃ (B : ℝ) (G : ℂ→ℂ), (∀ s,MeromorphicNFAt G s) ∧
      (∀ s,B<s.re → G s=odd (2*m) f 3 s) ∧
      ∀ s,G s=thirdReflectionMultiplier m η s*G (((2*m:ℕ):ℂ)-s) := by
  obtain ⟨B,G,hG,hagree,_hregular,hgerm⟩:=third_continuation m hm hf η hη hW hP
  have hη0 : η≠0 := by rcases hη with rfl|rfl <;> norm_num
  have hR : Differentiable ℂ (thirdReflectionMultiplier m η) := by
    unfold thirdReflectionMultiplier
    simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (234:ℂ)≠0)]
    fun_prop
  have hR0 (s : ℂ) : thirdReflectionMultiplier m η s≠0 :=
    mul_ne_zero (div_ne_zero hη0 (pow_ne_zero _ I_ne_zero))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  have hraw (s : ℂ) : thirdNumerator m f s/thirdFactor m f s=
      thirdReflectionMultiplier m η s*
        (thirdNumerator m f (((2*m:ℕ):ℂ)-s)/thirdFactor m f (((2*m:ℕ):ℂ)-s)) := by
    have hscalar : heckeScalar m f s≠0 := by
      intro h
      have hp:=heckeScalar_reflection_product m hf.toEulerData s
      rw [h,zero_mul] at hp
      exact zero_ne_one hp
    rw [thirdNumerator_reflection m hm hf η hη hW hP s,
      thirdFactor_reflection m hf.toEulerData s,mul_assoc,
      mul_div_mul_left _ _ (pow_ne_zero 3 hscalar)]
    ring
  have he:=QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => thirdNumerator m f s/thirdFactor m f s) G (thirdReflectionMultiplier m η)
    (((2*m:ℕ):ℂ)) hG (fun s => (hR.analyticAt s)) hR0 hgerm hraw
  exact ⟨B,G,hG,hagree,he⟩

#print axioms thirdNumerator_reflection
#print axioms third_reflection
end SmallLevelTwentySixOdd
end
end

/-! ## SmallLevelTwentySixThirdMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_third_conductor : Real.sqrt 234=3*Real.sqrt 26 := by
  rw [show (234:ℝ)=9*26 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem third_matrix_branch : fricke 26 (by decide)*
    SpecialLinearGroup.mapGL ℝ SmallLevelTwentySixGroup.Y*translation (1/3)=
      translation (1/3)*fricke 234 (by decide) := by
  have hs : (Real.sqrt 26)^2=26:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 26≠0:=(Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,SmallLevelTwentySixGroup.Y,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.map_apply,
      Fin.sum_univ_two,sqrt_third_conductor] <;>
    field_simp [hn] <;> norm_num [hs]

theorem third_matrix_conjugate : (fricke 26 (by decide))⁻¹*translation (1/3)*
    fricke 234 (by decide)*(translation (1/3))⁻¹=
      SpecialLinearGroup.mapGL ℝ SmallLevelTwentySixGroup.Y := by
  calc
    _=(fricke 26 (by decide))⁻¹*(translation (1/3)*fricke 234 (by decide))*
        (translation (1/3))⁻¹ := by group
    _=(fricke 26 (by decide))⁻¹*(fricke 26 (by decide)*
        SpecialLinearGroup.mapGL ℝ SmallLevelTwentySixGroup.Y*translation (1/3))*
        (translation (1/3))⁻¹ := by rw [third_matrix_branch]
    _=_ := by group

#print axioms third_matrix_conjugate
end SmallLevelTwentySixOdd
end
end

/-! ## SmallLevelTwentySixThirdAnalyticEndgameV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixOdd
open Complex Filter SmallLevelAdditive SmallLevelNormalized FinitenessOriginalFourier
  FinitenessFourierConstruction
open SmallLevelTwentySix (P)
open scoped Topology MatrixGroups ModularForm

/-- Exact analytic completion of the odd-third functional equation, once
an entire continuation has been supplied by the pole argument. -/
theorem third_coherent_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 26 (2*m) f ε)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f)
    (E : ℂ→ℂ) (BE : ℝ) (hE : Differentiable ℂ E)
    (hEF : ∀ s,BE<s.re → E s=odd (2*m) f 3 s) :
    ∃ (B : ℝ) (G : ℂ→ℂ), Differentiable ℂ G ∧ FinitenessOriginalInput.FiniteOrder G ∧
      (∀ s,B<s.re → G s=odd (2*m) f 3 s) ∧
      ∀ s,G s=ε*(234:ℂ)^((m:ℂ)-s)*G (((2*m:ℕ):ℂ)-s) := by
  obtain ⟨hη,hW⟩:=QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<26) m ε hε hlaw
  obtain ⟨B,G,hG,hGF,hFE⟩:=third_reflection m hm hf (ε*I^(2*m)) hη hW hP
  have hent : Differentiable ℂ G := by
    intro s
    apply AnalyticAt.differentiableAt
    exact SmallLevelSimplePoleTaylor.analyticAt_of_model
      (odd (2*m) f 3) G E E B BE (s.re-1) s hG hGF
      (fun z _ => (hE.analyticAt z).meromorphicAt) hEF
      (by linarith) (hE.analyticAt s) Filter.EventuallyEq.rfl
  refine ⟨B,G,hent,third_finiteOrder m hm hf (ε*I^(2*m)) hη hW hP hent B hGF,hGF,?_⟩
  intro s
  have he : ε*I^(2*m)/I^(2*m)=ε:=mul_div_cancel_right₀ _ (pow_ne_zero _ I_ne_zero)
  simpa only [thirdReflectionMultiplier,he] using hFE s

def thirdFourier (k : ℕ) (f : ℕ→ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/3:ℝ))-
    fourier (fullCoefficients f k) (z+(-1/3:ℝ))

theorem third_individual_law {k : ℕ} {f : ℕ→ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 26 k f ε)
    (hquad : ∀ z : ℂ,0<z.im → thirdFourier k f z=
      (ε*I^k)/(((Real.sqrt 234:ℂ)*z)^k)*thirdFourier k f (-1/((234:ℂ)*z))) :
    ∀ z : ℂ,0<z.im → fourier (fullCoefficients f k) (z+1/3)=
      (ε*I^k)/(((Real.sqrt 234:ℂ)*z)^k)*
        fourier (fullCoefficients f k) (-1/((234:ℂ)*z)+1/3) := by
  intro z hz
  have hr:=hlaw 3 (by decide) z hz
  have hroot : FinitenessNormalizedTwistProduct.root 26 f 3=1 := by
    norm_num [FinitenessNormalizedTwistProduct.root,FinitenessNormalizedTwistLocal.sign]
  rw [show Nat.lcm 26 (3^2)=234 by decide,hroot,one_mul,
    SmallLevelThree.twist_three _ (periodic _),SmallLevelThree.twist_three _ (periodic _)] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc:=hquad z hz
  norm_num only [thirdFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  linear_combination (hr+hc)/2

/-- The complete analytic/group endgame. The P law and an entire odd-third
continuation are supplied separately from the original pole system. -/
theorem modular_of_P_and_entire_third (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hP : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 26 f 2 • SmallLevelOriginal.fourierFunction (2*m) f)
    (E : ℂ→ℂ) (BE : ℝ) (hE : Differentiable ℂ E)
    (hEF : ∀ s,BE<s.re → E s=odd (2*m) f 3 s) :
    SmallLevelOriginal.IsModular 26 (2*m) f := by
  obtain ⟨ε,hε,hlaw⟩:=QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<26) hf
  obtain ⟨B,G,hent,hfinite,hGF,hFE⟩:=third_coherent_entire m hm hf ε hε hlaw hP E BE hE hEF
  obtain ⟨σ,_hσ,hgrowth⟩:=hf.growth
  have hquad : ∀ z : ℂ,0<z.im → thirdFourier (2*m) f z=
      (ε*I^(2*m))/(((Real.sqrt 234:ℂ)*z)^(2*m))*
        thirdFourier (2*m) f (-1/((234:ℂ)*z)) := by
    have h:=QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
      (k:=2*m) (ε:=ε) (B:=B) (by decide : 0<234) hf.zero hgrowth
      (1/3) 0 (-1/3) 0 G hent hfinite
      (by
        intro s hs
        rw [hGF s hs]
        norm_num only [odd,Nat.cast_ofNat,neg_div]
        ring)
      (by rcases hε with rfl|rfl <;> norm_num)
      (by
        have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
        simpa only [Nat.cast_ofNat,he] using hFE)
    intro z hz
    dsimp only at h
    unfold thirdFourier
    convert h z hz using 1 <;> ring
  have hF : ∀ z : ℂ,0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*I^(2*m))/(((Real.sqrt 26:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((26:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have h:=crossed_of_fricke 26 234 (2*m) (by decide) (by decide) (1/3) (1/3)
    _ (ε*I^(2*m)) hF (by
      intro z hz
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,
        Nat.cast_ofNat] using third_individual_law ε hlaw hquad z hz)
  rw [third_matrix_conjugate] at h
  exact SmallLevelTwentySixGroup.modular_of_P_G m hf hP h

#print axioms third_coherent_entire
#print axioms third_individual_law
#print axioms modular_of_P_and_entire_third
end SmallLevelTwentySixOdd
end
end
