module

public import FurstenbergDichotomyV1

set_option autoImplicit false

@[expose] public section

namespace SpanningExceptionalSet

open Set SpanningProjectedWords FurstenbergZero FurstenbergDichotomy
open IndependentBases

/-- The invariant exceptional set is finite by the classical Furstenberg theorem. -/
theorem exceptional_finite {Q q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {arc : Set Circle} (hopen : IsOpen arc)
    (hproper : exceptional Q q₁ q₂ arc ≠ univ) :
    (exceptional Q q₁ q₂ arc).Finite := by
  apply (finite_or_full h₁ h₂ hi (closed Q q₁ q₂ hopen) ?_).resolve_right hproper
  rintro n ⟨a,b,rfl⟩ x hx c d
  simpa only [smul_smul, pow_add, mul_assoc, mul_left_comm, mul_comm] using hx (c+a) (d+b)

/-- Finite invariant exceptional sets have a finite rational lift on [0,1].
Both endpoints are allowed, avoiding any discontinuity at the circle's cut. -/
theorem exceptional_rational_lifts {Q q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁)
    {arc : Set Circle} (hE : (exceptional Q q₁ q₂ arc).Finite) :
    ∃ F : Finset ℚ, ∀ x : ℝ, x ∈ Icc 0 1 → (x:Circle) ∈ exceptional Q q₁ q₂ arc →
      ∃ r ∈ F, (r:ℝ)=x := by
  classical
  let S : Set ℝ := Icc 0 1 ∩ ((↑) : ℝ → Circle) ⁻¹' exceptional Q q₁ q₂ arc
  have hS0 : (Ico 0 1 ∩ ((↑) : ℝ → Circle) ⁻¹' exceptional Q q₁ q₂ arc).Finite := by
    apply hE.of_injOn (fun x hx => hx.2)
    intro x hx y hy he
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=0) (by simpa using hx.1)
      (by simpa using hy.1)).mp he
  have hS : S.Finite := (hS0.union (finite_singleton 1)).subset (by
    intro x hx
    rcases lt_or_eq_of_le hx.1.2 with hl|rfl
    · exact Or.inl ⟨⟨hx.1.1,hl⟩,hx.2⟩
    · exact Or.inr rfl)
  have hr : ∀ x ∈ S, ∃ r : ℚ, (r:ℝ)=x := by
    intro x hx
    obtain ⟨d,hd,hxd⟩ := torsion_of_finite_invariant hE h₁
      (fun y hy => invariant_first Q q₁ q₂ arc hy) hx.2
    rw [← AddCircle.coe_nsmul,nsmul_eq_mul,AddCircle.coe_eq_zero_iff] at hxd
    obtain ⟨z,hz⟩ := hxd
    refine ⟨(z:ℚ)/(d:ℚ),?_⟩
    push_cast
    apply (div_eq_iff (by exact_mod_cast hd.ne' : (d:ℝ)≠0)).mpr
    simpa [zsmul_eq_mul,mul_comm] using hz
  let : Fintype S := hS.fintype
  let r : S → ℚ := fun x => Classical.choose (hr x.val x.property)
  refine ⟨Finset.univ.image r,?_⟩
  intro x hx he
  let a : S := ⟨x,hx,he⟩
  exact ⟨r a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,
    Classical.choose_spec (hr x a.property)⟩

/-- The periodic arc used in the trace proof. -/
def periodicArc (D : ℕ) : Set Circle := ((↑) : ℝ → Circle) '' Ioo 0 (1/(D:ℝ))

theorem periodicArc_open (D : ℕ) : IsOpen (periodicArc D) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

theorem zero_not_periodicArc {D : ℕ} (hD : 1 ≤ D) : (0:Circle) ∉ periodicArc D := by
  rintro ⟨t,ht,he⟩
  have hD' : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hbound : 1/(D:ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hD'
  have htI : t ∈ Ico (0:ℝ) (0+1) := ⟨ht.1.le,by simpa using ht.2.trans_le hbound⟩
  have ht0 : t=0 := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI (by simp)).mp he
  linarith [ht.1]

theorem periodicArc_proper_exceptional {Q D q₁ q₂ : ℕ} (hQ : 0<Q) (hD : 0<D) :
    exceptional Q q₁ q₂ (periodicArc D) ≠ univ := by
  let t : ℝ := 1/(2*(D:ℝ))
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  apply proper Q q₁ q₂ (x:=((t/(Q:ℝ):ℝ):Circle))
  rw [← AddCircle.coe_nsmul,nsmul_eq_mul,mul_div_cancel₀ _ hQr.ne']
  refine ⟨t,⟨by dsimp [t]; positivity,?_⟩,rfl⟩
  dsimp [t]
  apply one_div_lt_one_div_of_lt (by positivity)
  linarith

#print axioms exceptional_finite
#print axioms exceptional_rational_lifts
#print axioms periodicArc_proper_exceptional

end SpanningExceptionalSet
