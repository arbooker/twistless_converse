module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticPrimitiveResiduePair

/-- A unimodular residue row has coprime integer coordinates together with
the modulus. This avoids a quadratic search for Bezout witnesses in finite
matrix certificates. -/
theorem gcd_eq_one {N : ℕ} [NeZero N] (c d : ZMod N)
    (h : ∃ a b : ZMod N, a*d-b*c=1) :
    Nat.gcd (Nat.gcd c.val d.val) N = 1 := by
  obtain ⟨a,b,hab⟩ := h
  let g := Nat.gcd (Nat.gcd c.val d.val) N
  have hgN : (g : ℤ) ∣ (N : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right (Nat.gcd c.val d.val) N
  have hgc : (g : ℤ) ∣ (c.val : ℤ) := by
    exact_mod_cast dvd_trans (Nat.gcd_dvd_left (Nat.gcd c.val d.val) N)
      (Nat.gcd_dvd_left c.val d.val)
  have hgd : (g : ℤ) ∣ (d.val : ℤ) := by
    exact_mod_cast dvd_trans (Nat.gcd_dvd_left (Nat.gcd c.val d.val) N)
      (Nat.gcd_dvd_right c.val d.val)
  have he : (N : ℤ) ∣ (a.val : ℤ)*d.val-(b.val : ℤ)*c.val-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_zmod_val, hab, sub_self]
  have hp : (g : ℤ) ∣ (a.val : ℤ)*d.val-(b.val : ℤ)*c.val :=
    dvd_sub (dvd_mul_of_dvd_right hgd _) (dvd_mul_of_dvd_right hgc _)
  have h1 : (g : ℤ) ∣ 1 := by
    simpa only [sub_sub_cancel] using dvd_sub hp (dvd_trans hgN he)
  have hn : g ∣ 1 := by exact_mod_cast h1
  exact Nat.dvd_one.mp hn

#print axioms gcd_eq_one
end QuantitativeArithmeticPrimitiveResiduePair
