module

public import AsymptoticCongruenceWeightRemovalV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticOrbitDecode AsymptoticCompactBranch AsymptoticIntegralSubgroup
open ContinuousLinearMap
open scoped lp

theorem weight_fold (N : ℕ) (ε : ℝ) (t : ℕ) (x : ℍ) (g : AsymptoticRationalGroup.Group) :
    weight N ε t (foldLabel x g • x)=weight N ε t (g • x) := by
  let h : gamma N := ⟨translationLabel ((-Int.floor (g • x).re:ℤ):ℚ),translation_mem N _⟩
  simpa only [foldLabel,mul_smul,h,Int.cast_neg] using weight_invariant N ε t h (g • x)

theorem cap_fold (ε : ℝ) (t : ℕ) (x : ℍ) (g : AsymptoticRationalGroup.Group) :
    cap ε t (foldLabel x g • x)=cap ε t (g • x) := by
  simp only [foldLabel,mul_smul,AsymptoticCompactTranslation.cap_translate]

/-- A single normalized quotient coordinate is a bounded functional
on the full orbit Hilbert space, even though their aggregate unweighted
function need not be square summable. -/
noncomputable def coordinate (N : ℕ) (ε : ℝ) (t : ℕ) (x : ℍ)
    (g : AsymptoticRationalGroup.Group) : ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℂ :=
  ((Real.sqrt (weight N ε t (g • x)):ℂ)/(cap ε t (g • x):ℂ)) •
    lp.evalCLM ℂ (fun _ : AsymptoticRationalGroup.Group => ℂ) 2 (foldLabel x g)

theorem coordinate_apply (N : ℕ) (ε : ℝ) (t : ℕ) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (g : AsymptoticRationalGroup.Group) :
    coordinate N ε t x g v=(Real.sqrt (weight N ε t (g • x)):ℂ)*decode ε t x v g := by
  change ((Real.sqrt (weight N ε t (g • x)):ℂ)/(cap ε t (g • x):ℂ))*v (foldLabel x g)=_
  rw [decode]
  ring

theorem coordinate_induction (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (f : ℓ²(Classes N,ℂ)) (g : AsymptoticRationalGroup.Group) :
    coordinate N ε t x g (induction N hε ht x f)=f (classOf N g) := by
  rw [coordinate_apply,decode,induction_apply,amplitude,
    Set.indicator_of_mem (foldLabel_mem x g),foldLabel_class,cap_fold,weight_fold,Complex.ofReal_div]
  have hc := cap_ne_zero hε t (g • x)
  have hw : (Real.sqrt (weight N ε t (g • x)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (weight_pos N hε ht _)).ne'
  field_simp

/-- Pointwise multiplication by a congruence-invariant function
preserves the quotient space whenever the resulting vector is in l2.
No boundedness hypothesis on the multiplier is needed. -/
theorem pointwise_weight_preserves_quotient (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (b : ℍ → ℂ) (hb : ∀ h : gamma N,∀ x,b (h.val • x)=b x)
    (x : ℍ) (u v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (hu : u∈quotientSpace N hε ht x)
    (hv : ∀ g,v g=b (g • x)*u g) : v∈quotientSpace N hε ht x := by
  obtain ⟨f,rfl⟩ := hu
  change ∀ g,v g=b (g • x)*induction N hε ht x f g at hv
  have hi (h : gamma N) (g : AsymptoticRationalGroup.Group) :
      b ((h.val*g) • x)*f (classOf N (h.val*g))=b (g • x)*f (classOf N g) := by
    simp only [mul_smul,hb,classOf_mul]
  obtain ⟨F,hF⟩ := factors N (fun g => b (g • x)*f (classOf N g)) hi
  change v∈(AsymptoticFiberIsometry.linear (classOf N) (fun g => amplitude N ε t (g • x))
    (fibre_amplitude_hasSum N hε ht x)).range
  apply (AsymptoticFiberIsometry.range_iff _ _ _ v).mpr
  refine ⟨F,?_⟩
  intro g
  rw [hv g,induction_apply,← hF g]
  ring

/-- The actual inverse square-root multiplier removes precisely the
normalization in the quotient coordinates. -/
theorem coordinate_normalizer (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (u v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : ∀ g,v g=(normalizer N ε t (g • x):ℂ)*u g) (g : AsymptoticRationalGroup.Group) :
    coordinate N ε t x g v=decode ε t x u g := by
  rw [coordinate_apply,decode,hv,normalizer,weight_fold,Complex.ofReal_inv]
  rw [decode]
  have hc := cap_ne_zero hε t (g • x)
  have hw : (Real.sqrt (weight N ε t (g • x)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (weight_pos N hε ht _)).ne'
  field_simp

#print axioms weight_fold
#print axioms cap_fold
#print axioms coordinate_apply
#print axioms coordinate_induction
#print axioms pointwise_weight_preserves_quotient
#print axioms coordinate_normalizer

end AsymptoticCongruenceQuotient
