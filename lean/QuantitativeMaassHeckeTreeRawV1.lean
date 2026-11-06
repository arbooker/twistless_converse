module

public import QuantitativeMaassHeckeTreeWalksV1
public import Mathlib.Algebra.Group.Int.Units

set_option autoImplicit false
@[expose] public section

open scoped BigOperators

namespace QuantitativeMaass
namespace HeckeUpper

def scale (c : ℤ) (M : HeckeUpper) : HeckeUpper := ⟨c*M.a,c*M.b,c*M.d⟩

/-- An integral upper-triangular matrix represents an integer translation
precisely when its two diagonal entries agree and divide its upper entry. -/
def translation (M : HeckeUpper) : Prop := M.a = M.d ∧ M.d ∣ M.b

instance (M : HeckeUpper) : Decidable M.translation := inferInstanceAs (Decidable (_ ∧ _))

theorem translation_scale_iff (c : ℤ) (hc : c ≠ 0) (M : HeckeUpper) :
    (scale c M).translation ↔ M.translation := by
  constructor
  · rintro ⟨ha, ⟨k, hb⟩⟩
    refine ⟨mul_left_cancel₀ hc ha, k, ?_⟩
    apply mul_left_cancel₀ hc
    simpa only [scale, mul_assoc] using hb
  · rintro ⟨ha, k, hb⟩
    refine ⟨by change c*M.a = c*M.d; rw [ha], k, ?_⟩
    change c*M.b = c*M.d*k
    rw [hb, mul_assoc]

theorem left_scale (p : ℕ) (j : Option (ZMod p)) (c : ℤ) (M : HeckeUpper) :
    left p j (scale c M) = scale c (left p j M) := by
  cases j <;> simp only [left, scale]
  all_goals congr 1 <;> ring

theorem cancel_restore (p : ℕ) (j : Option (ZMod p)) (M : HeckeUpper)
    (hc : cancels p j M) : scale p (next p j M) = left p j M := by
  rw [next_of_cancel p j M hc]
  change (p : ℤ) ∣ (left p j M).a ∧ (p : ℤ) ∣ (left p j M).b ∧
    (p : ℤ) ∣ (left p j M).d at hc
  generalize hL : left p j M = L at *
  rcases L with ⟨a,b,d⟩
  obtain ⟨ha,hb,hd⟩ := hc
  simp only [scale]
  congr 1
  · simpa only [mul_comm] using Int.ediv_mul_cancel ha
  · simpa only [mul_comm] using Int.ediv_mul_cancel hb
  · simpa only [mul_comm] using Int.ediv_mul_cancel hd

theorem primitive_translation_iff (p : ℕ) [Fact p.Prime] (M : HeckeUpper)
    (hM : primitive p M) (k : ℕ) (hdet : M.det = (p : ℤ)^k) :
    M.translation ↔ M.det = 1 := by
  constructor
  · rintro ⟨ha,hb⟩
    cases k with
    | zero => simpa using hdet
    | succ k =>
      have hpdet : (p : ℤ) ∣ M.det := by
        rw [hdet, pow_succ']
        exact dvd_mul_right _ _
      have hsq : (M.d : ZMod p) * (M.d : ZMod p) = 0 := by
        rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa only [det, ha] using hpdet
      have hd : (p : ℤ) ∣ M.d :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd M.d p).mp (mul_self_eq_zero.mp hsq)
      exact False.elim (hM ⟨ha ▸ hd, hd.trans hb, hd⟩)
  · intro hd
    obtain ⟨ha,hd⟩ | ⟨ha,hd⟩ := Int.eq_one_or_neg_one_of_mul_eq_one' hd
    · simp [translation, ha, hd]
    · simp [translation, ha, hd]

/-- Count the original matrix products before any scalar normalization. -/
noncomputable def rawWalks (p : ℕ) [Fact p.Prime] : ℕ → HeckeUpper → ℕ
  | 0, M => if M.translation then 1 else 0
  | n + 1, M => ∑ j : Option (ZMod p), rawWalks p n (left p j M)

theorem rawWalks_scale (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℤ) (hc : c ≠ 0)
    (M : HeckeUpper) : rawWalks p n (scale c M) = rawWalks p n M := by
  induction n generalizing M with
  | zero => simp only [rawWalks, translation_scale_iff c hc]
  | succ n ih => simp only [rawWalks, left_scale, ih]

theorem rawWalks_left_eq_next (p : ℕ) [Fact p.Prime] (n : ℕ)
    (j : Option (ZMod p)) (M : HeckeUpper) :
    rawWalks p n (left p j M) = rawWalks p n (next p j M) := by
  by_cases hc : cancels p j M
  · rw [← cancel_restore p j M hc]
    apply rawWalks_scale
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  · rw [next_of_not_cancel p j M hc]

theorem next_det_power (p : ℕ) [Fact p.Prime] (j : Option (ZMod p))
    (M : HeckeUpper) (k : ℕ) (hdet : M.det = (p : ℤ)^k) :
    ∃ k' : ℕ, (next p j M).det = (p : ℤ)^k' := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases hc : cancels p j M
  · cases k with
    | zero =>
      have hp1 : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast (Fact.out : p.Prime).not_dvd_one
      exact False.elim (no_cancel p M (by simpa only [hdet, pow_zero] using hp1) j hc)
    | succ k =>
      refine ⟨k, mul_left_cancel₀ hpne ?_⟩
      rw [next_det_cancel p hpne j M hc, hdet, pow_succ']
  · refine ⟨k+1, ?_⟩
    rw [next_det_forward p j M hc, hdet, pow_succ']

/-- Normalization does not change the exact count of projective integer
translations among the original branch words. -/
theorem rawWalks_eq_walks (p : ℕ) [Fact p.Prime] (n k : ℕ) (M : HeckeUpper)
    (hM : primitive p M) (hdet : M.det = (p : ℤ)^k) :
    rawWalks p n M = walks p n M := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  induction n generalizing k M with
  | zero => simp only [rawWalks, walks, primitive_translation_iff p M hM k hdet]
  | succ n ih =>
    simp only [rawWalks, walks]
    apply Finset.sum_congr rfl
    intro j _
    rw [rawWalks_left_eq_next]
    obtain ⟨k',hk'⟩ := next_det_power p j M k hdet
    exact ih k' _ (next_primitive p hpne j M hM) hk'

theorem rawWalks_root_eq_tree (p n : ℕ) [Fact p.Prime] :
    rawWalks p n root = treeWalkCount (p+1) n 0 := by
  rw [rawWalks_eq_walks p n 0 root (root_primitive p) (by simp [root_det]), walks_root_eq_tree]

#print axioms primitive_translation_iff
#print axioms rawWalks_eq_walks
#print axioms rawWalks_root_eq_tree

end HeckeUpper
end QuantitativeMaass
