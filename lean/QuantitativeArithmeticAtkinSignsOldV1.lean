module

public import QuantitativeArithmeticAtkinSignsLowerV1
public import QuantitativeNewGapTreeArithmeticDilationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticAtkinSigns

open Matrix AsymptoticAtkinLehner AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalCusp AsymptoticRationalGroup QuantitativeNewGap
open scoped MatrixGroups

private theorem subgroup_conj_iff {G : Type*} [_root_.Group G] (H : Subgroup G) (a : G) (ha : a∈H) (g : G) :
    g∈H ↔ a*g*a⁻¹∈H := by
  constructor
  · intro hg
    exact H.mul_mem (H.mul_mem ha hg) (H.inv_mem ha)
  · intro hg
    have hh := H.mul_mem (H.mul_mem (H.inv_mem ha) hg) ha
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hh

private theorem conjugation_iff_of_square {G : Type*} [_root_.Group G] (H : Subgroup G) (a : G)
    (hs : a*a∈H) (hf : ∀g∈H,a*g*a⁻¹∈H) (g : G) : g∈H ↔ a*g*a⁻¹∈H := by
  constructor
  · exact hf g
  · intro hg
    have hh := hf _ hg
    have he : a*(a*g*a⁻¹)*a⁻¹=(a*a)*g*(a*a)⁻¹ := by group
    rw [he] at hh
    exact (subgroup_conj_iff H (a*a) hs g).mpr hh

/-- The local Atkin element exchanges its own two literal old directions. -/
theorem own_first_iff (M p : ℕ) (hM : 0<M) (hp : 0<p) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (g : AsymptoticRationalGroup.Group) :
    g∈gamma M ↔ localAtkin M p hM hp A B hAB*g*(localAtkin M p hM hp A B hAB)⁻¹∈
      degeneracyGroup M p hp := by
  rw [mem_degeneracy_iff_dilation,localAtkin_eq_dilation_inv]
  have he : dilationLabel p hp*((dilationLabel p hp)⁻¹*integralLabel (heckeSL M p A B hAB)*g*
      ((dilationLabel p hp)⁻¹*integralLabel (heckeSL M p A B hAB))⁻¹)*(dilationLabel p hp)⁻¹=
      integralLabel (heckeSL M p A B hAB)*g*(integralLabel (heckeSL M p A B hAB))⁻¹ := by group
  rw [he]
  exact subgroup_conj_iff (gamma M) _ ⟨_,heckeSL_mem M p A B hAB,rfl⟩ g

theorem own_second_iff (M p : ℕ) (hM : 0<M) (hp : 0<p) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (g : AsymptoticRationalGroup.Group) :
    g∈degeneracyGroup M p hp ↔ localAtkin M p hM hp A B hAB*g*(localAtkin M p hM hp A B hAB)⁻¹∈
      gamma M := by
  let W := localAtkin M p hM hp A B hAB
  have hs : W*W∈degeneracyGroup M p hp :=
    gamma_le_degeneracyGroup M p hM hp (localAtkin_square_mem M p hM hp A B hAB)
  have he := own_first_iff M p hM hp A B hAB (W*g*W⁻¹)
  change W*g*W⁻¹∈gamma M ↔ W*(W*g*W⁻¹)*W⁻¹∈degeneracyGroup M p hp at he
  have hx : W*(W*g*W⁻¹)*W⁻¹=(W*W)*g*(W*W)⁻¹ := by group
  rw [hx] at he
  exact (subgroup_conj_iff (degeneracyGroup M p hp) (W*W) hs g).trans he.symm

theorem lower_first_conj_mem (L q p : ℕ) (hL : 0<L) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1)
    (g : AsymptoticRationalGroup.Group) (hg : g∈gamma (p*L)) :
    localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB*g*
      (localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB)⁻¹∈gamma (p*L) := by
  rw [localAtkin_lower L q p hL hq hp A B hAB]
  let E := integralLabel (localAtkinLowerSL L q p A B hAB)
  let W := localAtkin L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)
  have hE : E∈gamma (p*L) := ⟨_,localAtkinLowerSL_mem L q p A B hAB,rfl⟩
  have hh := (subgroup_conj_iff (gamma (p*L)) E hE (W*g*W⁻¹)).mp
    (local_conj_mem L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB) hg)
  convert hh using 1
  dsimp [E,W]
  group

theorem lower_second_conj_mem (L q p : ℕ) (hL : 0<L) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1)
    (g : AsymptoticRationalGroup.Group) (hg : g∈degeneracyGroup (p*L) q hq) :
    localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB*g*
      (localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB)⁻¹∈degeneracyGroup (p*L) q hq := by
  rw [mem_degeneracy_iff_dilation] at hg ⊢
  let W := localAtkin L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB)
  let D := dilationLabel q hq
  have he : localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB=D⁻¹*W*D := by
    have hh := localAtkin_lower_dilation L q p hL hq hp A B hAB
    apply (mul_left_cancel (a:=D))
    simpa only [mul_assoc,mul_inv_cancel_left] using hh
  rw [he]
  have hh := local_conj_mem L p hL hp A ((q:ℤ)*B) (localAtkin_lower_bezout L q p A B hAB) hg
  convert hh using 1
  dsimp [D,W]
  group

theorem lower_first_iff (L q p : ℕ) (hL : 0<L) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1) (g : AsymptoticRationalGroup.Group) :
    g∈gamma (p*L) ↔ localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB*g*
      (localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB)⁻¹∈gamma (p*L) := by
  apply conjugation_iff_of_square
  · apply gamma_le_of_dvd (show p*L∣p*(q*L) from ⟨q,by ring⟩)
    exact localAtkin_square_mem (q*L) p (Nat.mul_pos hq hL) hp A B hAB
  · exact lower_first_conj_mem L q p hL hq hp A B hAB

theorem lower_second_iff (L q p : ℕ) (hL : 0<L) (hq : 0<q) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((q*L:ℕ):ℤ)*B=1) (g : AsymptoticRationalGroup.Group) :
    g∈degeneracyGroup (p*L) q hq ↔ localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB*g*
      (localAtkin (q*L) p (Nat.mul_pos hq hL) hp A B hAB)⁻¹∈degeneracyGroup (p*L) q hq := by
  apply conjugation_iff_of_square
  · apply gamma_le_degeneracyGroup (p*L) q (Nat.mul_pos hp hL) hq
    simpa only [Nat.mul_left_comm] using localAtkin_square_mem (q*L) p (Nat.mul_pos hq hL) hp A B hAB
  · exact lower_second_conj_mem L q p hL hq hp A B hAB

#print axioms own_first_iff
#print axioms own_second_iff
#print axioms lower_first_iff
#print axioms lower_second_iff

end QuantitativeArithmeticAtkinSigns
