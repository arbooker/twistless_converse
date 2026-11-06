module

public import FurstenbergSemigroupV1
public import SpanningExceptionalSetV1

set_option autoImplicit false

@[expose] public section

namespace FurstenbergZero

open SpanningProjectedWords SpanningExceptionalSet FurstenbergSemigroup
open IndependentBases Set

def Invariant (q₁ q₂ : ℕ) (A : Set Circle) : Prop :=
  ∀ n, Tower q₁ q₂ n → ∀ x ∈ A, n • x ∈ A

/-- One-sided accumulation at zero suffices for the closed invariant set
to fill the circle. The proof approximates positive real representatives
using the multiplicative net, then uses closedness. -/
theorem full_of_positive_lifts {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {A : Set Circle} (hA : IsClosed A)
    (hInv : Invariant q₁ q₂ A)
    (hzero : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, 0 < t ∧ t < δ ∧ (t:Circle) ∈ A) :
    A = univ := by
  let S : Set ℝ := ((↑) : ℝ → Circle) ⁻¹' A
  have hS : IsClosed S := hA.preimage (AddCircle.continuous_mk' 1)
  have hall : ∀ y : ℝ, 0 < y → (y:Circle) ∈ A := by
    intro y hy
    apply hS.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro η hη
    obtain ⟨X,hX,hnet⟩ := multiplicative_net h₁ h₂ hi (div_pos hη hy)
    obtain ⟨t,ht,htX,htA⟩ := hzero (y/X) (div_pos hy hX)
    have hyt : X ≤ y/t := (le_div_iff₀ ht).mpr (by
      have he := (lt_div_iff₀ hX).mp htX
      nlinarith)
    obtain ⟨u,hu,hlo,hup⟩ := hnet (y/t) hyt
    have hlow : y < (u:ℝ)*t := (div_lt_iff₀ ht).mp hlo
    have hupp : (u:ℝ)*t < y+η := by
      have he := mul_lt_mul_of_pos_right hup ht
      have hid : (1+η/y)*(y/t)*t = y+η := by field_simp
      rwa [hid] at he
    refine ⟨(u:ℝ)*t, ?_, ?_⟩
    · change (((u:ℝ)*t:ℝ):Circle) ∈ A
      simpa only [← nsmul_eq_mul, AddCircle.coe_nsmul] using hInv u hu (t:Circle) htA
    · rw [Real.dist_eq, abs_of_neg (by linarith : y-(u:ℝ)*t < 0)]
      linarith
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ ((↑) : ℝ → Circle) '' Ioc 0 (0+1) := by
    rw [AddCircle.coe_image_Ioc_eq]
    trivial
  obtain ⟨y,hy,rfl⟩ := hx
  exact hall y hy.1

/-- Furstenberg's accumulation-at-zero lemma, first in a real-lift form. -/
theorem full_of_small_nonzero_lifts {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {A : Set Circle} (hA : IsClosed A)
    (hInv : Invariant q₁ q₂ A)
    (hzero : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, 0 < |t| ∧ |t| < δ ∧ (t:Circle) ∈ A) :
    A = univ := by
  classical
  by_cases hpos : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, 0 < t ∧ t < δ ∧ (t:Circle) ∈ A
  · exact full_of_positive_lifts h₁ h₂ hi hA hInv hpos
  push Not at hpos
  obtain ⟨δ,hδ,hδA⟩ := hpos
  let B : Set Circle := (fun x => -x) ⁻¹' A
  have hB : IsClosed B := hA.preimage continuous_neg
  have hBInv : Invariant q₁ q₂ B := by
    intro n hn x hx
    change -(n • x) ∈ A
    rw [← smul_neg]
    exact hInv n hn (-x) hx
  have hBzero : ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧ (t:Circle) ∈ B := by
    intro η hη
    obtain ⟨t,ht,htsmall,htA⟩ := hzero (min δ η) (lt_min hδ hη)
    have htδ := htsmall.trans_le (min_le_left _ _)
    have htη := htsmall.trans_le (min_le_right _ _)
    have htneg : t < 0 := by
      by_contra h
      have htpos : 0 < t := by rw [abs_of_nonneg (by linarith)] at ht; exact ht
      exact hδA t htpos ((le_abs_self t).trans_lt htδ) htA
    refine ⟨-t,by linarith,by simpa [abs_of_neg htneg] using htη,?_⟩
    simpa only [B, mem_preimage, AddCircle.coe_neg, neg_neg] using htA
  have hfull := full_of_positive_lifts h₁ h₂ hi hB hBInv hBzero
  apply eq_univ_of_forall
  intro x
  have hx : -x ∈ B := hfull.symm ▸ mem_univ _
  simpa only [B, mem_preimage, neg_neg] using hx

/-- A non-isolated zero supplies arbitrarily small nonzero real lifts. -/
theorem small_nonzero_lifts {A : Set Circle} (hzero : (0:Circle) ∈ closure (A \ {0})) :
    ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, 0 < |t| ∧ |t| < δ ∧ (t:Circle) ∈ A := by
  intro δ hδ
  let U := ((↑) : ℝ → Circle) '' Ioo (-δ) δ
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have h0U : (0:Circle) ∈ U := ⟨0,⟨by linarith,hδ⟩,rfl⟩
  obtain ⟨x,hxU,hxA⟩ := mem_closure_iff.mp hzero U hU h0U
  obtain ⟨t,ht,rfl⟩ := hxU
  have htne : t ≠ 0 := by
    intro he
    subst t
    exact hxA.2 (mem_singleton 0)
  exact ⟨t,abs_pos.mpr htne,abs_lt.mpr ht,hxA.1⟩

/-- The classical closed-invariant-set accumulation-at-zero result. -/
theorem full_of_zero_accumulation {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {A : Set Circle} (hA : IsClosed A)
    (hInv : Invariant q₁ q₂ A) (hzero : (0:Circle) ∈ closure (A \ {0})) :
    A = univ :=
  full_of_small_nonzero_lifts h₁ h₂ hi hA hInv (small_nonzero_lifts hzero)

#print axioms full_of_zero_accumulation

end FurstenbergZero
