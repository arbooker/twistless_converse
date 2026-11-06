module

public import SpanningProjectedWordsV1
public import CobhamClosePowersV1
public import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

@[expose] public section

namespace FurstenbergSemigroup

open SpanningProjectedWords IndependentBases

/-- Independent bases give two distinct, arbitrarily close tower elements. -/
theorem close_elements {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℕ, Tower q₁ q₂ a ∧ Tower q₁ q₂ b ∧ 0 < a ∧ a < b ∧
      (b:ℝ) < (1+ε)*(a:ℝ) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1/ε) 1)
  have hKpos : (0:ℝ) < K := lt_trans (by norm_num) ((le_max_right _ _).trans_lt hK)
  have hKε : 1 < (K:ℝ)*ε := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hK)
  obtain ⟨m,n,hm,hn,hab,hba⟩ := CobhamClosePowers.close_powers h₁ h₂ K
  have hne : q₁^m ≠ q₂^n := fun he => (by have := (hi m n he).1; omega)
  have hq₁ : 0 < q₁^m := pow_pos (by omega) _
  have hq₂ : 0 < q₂^n := pow_pos (by omega) _
  have hbound : ∀ a b : ℕ, 0 < a → K*b < (K+1)*a →
      (b:ℝ) < (1+ε)*(a:ℝ) := by
    intro a b ha hab
    have ha' : (0:ℝ) < a := by exact_mod_cast ha
    have hab' : (K:ℝ)*b < ((K:ℝ)+1)*a := by exact_mod_cast hab
    have hsmall := mul_lt_mul_of_pos_right hKε ha'
    nlinarith
  rcases lt_or_gt_of_ne hne with hlt|hlt
  · exact ⟨q₁^m,q₂^n,⟨m,0,by simp⟩,⟨0,n,by simp⟩,
      hq₁,hlt,hbound _ _ hq₁ hba⟩
  · exact ⟨q₂^n,q₁^m,⟨0,n,by simp⟩,⟨m,0,by simp⟩,
      hq₂,hlt,hbound _ _ hq₂ hab⟩

/-- Above a fixed threshold the two-generator semigroup meets every
multiplicative interval (x,(1+ε)x). This is the non-lacunarity estimate
needed in Furstenberg's elementary accumulation-at-zero argument. -/
theorem multiplicative_net {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 0 < X ∧ ∀ x : ℝ, X ≤ x →
      ∃ u : ℕ, Tower q₁ q₂ u ∧ x < u ∧ (u:ℝ) < (1+ε)*x := by
  obtain ⟨a,b,ha,hb,hapos,hab,hclose⟩ := close_elements h₁ h₂ hi hε
  have haR : (0:ℝ) < a := by exact_mod_cast hapos
  have hqR : (1:ℝ) < q₁ := by exact_mod_cast h₁
  let r : ℝ := (b:ℝ)/a
  have hr : 1 < r := (lt_div_iff₀ haR).mpr (by simpa using (show (a:ℝ) < b by exact_mod_cast hab))
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hrclose : r < 1+ε := (div_lt_iff₀ haR).mpr (by nlinarith [hclose])
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (q₁:ℝ) hr
  let X : ℝ := (a:ℝ)^M
  have hX : 0 < X := pow_pos haR _
  refine ⟨X,hX,?_⟩
  intro x hx
  have hxpos : 0 < x := hX.trans_le hx
  obtain ⟨j,hj₀,hj₁⟩ := exists_nat_pow_near ((le_div_iff₀ hX).mpr (by simpa using hx)) hqR
  let c : ℝ := X*(q₁:ℝ)^j
  have hc : 0 < c := mul_pos hX (pow_pos (by linarith) _)
  have hcx : c ≤ x := by
    dsimp [c]
    nlinarith [(le_div_iff₀ hX).mp hj₀]
  have hxc : x < c*q₁ := by
    have he := (div_lt_iff₀ hX).mp hj₁
    rw [pow_succ] at he
    dsimp [c]
    nlinarith
  obtain ⟨i,hi₀,hi₁⟩ := exists_nat_pow_near ((le_div_iff₀ hc).mpr (by simpa using hcx)) hr
  have hiM : i < M := by
    by_contra hn
    have hpow := pow_le_pow_right₀ hr.le (le_of_not_gt hn)
    have hz : x/c < (q₁:ℝ) := (div_lt_iff₀ hc).mpr (by nlinarith [hxc])
    linarith
  let u := a^(M-(i+1))*b^(i+1)*q₁^j
  have hu : Tower q₁ q₂ u := tower_mul
    (tower_mul (tower_pow ha _) (tower_pow hb _)) ⟨j,0,by simp⟩
  have huc : (u:ℝ) = c*r^(i+1) := by
    have haPow : (a:ℝ)^M = (a:ℝ)^(M-(i+1))*(a:ℝ)^(i+1) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    dsimp [u,c,X,r]
    push_cast
    rw [haPow, div_pow]
    field_simp
  refine ⟨u,hu,?_,?_⟩
  · rw [huc]
    have he := (div_lt_iff₀ hc).mp hi₁
    nlinarith
  · rw [huc, pow_succ]
    have he := (le_div_iff₀ hc).mp hi₀
    have hmul := mul_le_mul_of_nonneg_right he hrpos.le
    have hfinal := mul_lt_mul_of_pos_right hrclose hxpos
    nlinarith

#print axioms close_elements
#print axioms multiplicative_net

end FurstenbergSemigroup
