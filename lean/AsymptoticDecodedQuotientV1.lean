module

public import AsymptoticCongruenceQuotientV1
public import AsymptoticOrbitDecodeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticOrbitDecode AsymptoticCompactBranch AsymptoticMassTransport
open AsymptoticIntegralSubgroup AsymptoticCongruenceLabels
open scoped lp

theorem factors (N : ℕ) (F : AsymptoticRationalGroup.Group → ℂ)
    (hF : ∀ h : gamma N,∀ g,F (h.val*g)=F g) :
    ∃ f : Classes N → ℂ,∀ g,F g=f (classOf N g) := by
  have he : ∀ a b,QuotientGroup.rightRel (gamma N) a b → F a=F b := by
    intro a b hab
    let h : gamma N := ⟨b*a⁻¹,QuotientGroup.rightRel_apply.mp hab⟩
    simpa only [h,inv_mul_cancel_right] using (hF h a).symm
  exact ⟨Quotient.lift F he,fun _ => rfl⟩

theorem foldLabel_mem (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    foldLabel z g • z∈strip := by
  change (translationLabel (-(Int.floor (g • z).re:ℚ))*g) • z∈strip
  rw [mul_smul]
  have hr : (translationLabel (-(Int.floor (g • z).re:ℚ)) • (g • z)).re=
      (g • z).re-(Int.floor (g • z).re:ℝ) := by
    simpa only [Int.cast_neg,sub_eq_add_neg] using
      translation_re (-Int.floor (g • z).re) (g • z)
  change 0≤(translationLabel (-(Int.floor (g • z).re:ℚ)) • (g • z)).re ∧
    (translationLabel (-(Int.floor (g • z).re:ℚ)) • (g • z)).re<1
  rw [hr]
  constructor <;> linarith [Int.floor_le (g • z).re,Int.lt_floor_add_one (g • z).re]

theorem foldLabel_class (N : ℕ) (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    classOf N (foldLabel z g)=classOf N g := by
  let h : gamma N := ⟨translationLabel ((-Int.floor (g • z).re:ℤ):ℚ),
    translation_mem N _⟩
  simpa only [foldLabel,h,Int.cast_neg] using classOf_mul N h g

theorem foldLabel_self (z : ℍ) (g : AsymptoticRationalGroup.Group) (hg : g • z∈strip) :
    foldLabel z g=g := by
  have hf : Int.floor (g • z).re=0 := Int.floor_eq_zero_iff.mpr hg
  have hz : translationLabel (0:ℚ)=1 := by
    apply mul_left_cancel (a:=translationLabel (0:ℚ))
    simpa using translationLabel_mul (0:ℚ) 0
  simp only [foldLabel,hf,Int.cast_zero,neg_zero,hz,one_mul]

/-- An invariant decoded strip vector belongs to the induced quotient
Hilbert space. Square summability of its quotient coordinates is a
consequence of fibre normalization, not an additional hypothesis. -/
theorem range_of_decode (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : ∀ g,g • z∉strip → v g=0)
    (hΓ : ∀ h : gamma N,∀ g,decode ε t z v (h.val*g)=decode ε t z v g) :
    v∈(induction N hε ht z).toLinearMap.range := by
  let F : AsymptoticRationalGroup.Group → ℂ := fun g =>
    (Real.sqrt (weight N ε t (g • z)):ℂ)*decode ε t z v g
  have hF : ∀ h : gamma N,∀ g,F (h.val*g)=F g := by
    intro h g
    simp only [F,mul_smul,weight_invariant,hΓ]
  obtain ⟨f,hf⟩ := factors N F hF
  change v∈(AsymptoticFiberIsometry.linear (classOf N)
    (fun g => amplitude N ε t (g • z)) (fibre_amplitude_hasSum N hε ht z)).range
  apply (AsymptoticFiberIsometry.range_iff _ _ _ v).mpr
  refine ⟨f,?_⟩
  intro g
  classical
  by_cases hg : g • z∈strip
  · rw [← hf g]
    dsimp only [F]
    rw [amplitude,Set.indicator_of_mem hg,Complex.ofReal_div,decode,foldLabel_self z g hg]
    have hs : (Real.sqrt (weight N ε t (g • z)):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (weight_pos N hε ht _)).ne'
    have hc := cap_ne_zero hε t (g • z)
    field_simp
  · rw [hv g hg,amplitude,Set.indicator_of_notMem hg,zero_mul]

#print axioms factors
#print axioms foldLabel_mem
#print axioms foldLabel_class
#print axioms foldLabel_self
#print axioms range_of_decode

end AsymptoticCongruenceQuotient
