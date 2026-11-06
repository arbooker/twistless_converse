module

public import CompleteRowCosetsV1
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace GridCarrier

open SpanningCyclicCoordinates CompleteRowCosets

theorem equal_of_close_modEq {m x y : ℤ} (hm : 0<m) (h : Int.ModEq m x y)
    (hclose : |y-x|<m) : x=y := by
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp h
  rw [hk,abs_mul,abs_of_pos hm] at hclose
  have hk1 : |k|<1 := by nlinarith
  have hk0 : k=0 := by have := abs_lt.mp hk1; omega
  rw [hk0,mul_zero] at hk
  omega

theorem offset_separation {m w r z c t t' J : ℤ} (hw : 0<w) (hJ : 2*J<w)
    (ht : |t|≤J) (ht' : |t'|≤J)
    (h : Int.ModEq (m*w) (z*(r*w)+t') (c*w+t)) : t'=t := by
  have hh := h.of_dvd (dvd_mul_left w m)
  have hleft : Int.ModEq w (z*(r*w)+t') t' := by
    rw [←mul_assoc]
    simp [Int.ModEq]
  have hright : Int.ModEq w (c*w+t) t := by simp [Int.ModEq]
  apply equal_of_close_modEq hw (hleft.symm.trans (hh.trans hright))
  have hhabs := abs_sub t t'
  omega

abbrev Offsets (J : ℕ) := ↥(Finset.Icc (-(J:ℤ)) (J:ℤ))

theorem row_incidence_iff {m w r z c t t' J : ℤ} (hw : 0<w) (hJ : 2*J<w)
    (ht : |t|≤J) (ht' : |t'|≤J) :
    Int.ModEq (m*w) (z*(r*w)+t') (c*w+t) ↔
      t'=t ∧ Int.ModEq m (z*r) c := by
  constructor
  · intro h
    have he := offset_separation hw hJ ht ht' h
    refine ⟨he,?_⟩
    rw [he] at h
    have hh := h.add_right_cancel' t
    rw [←mul_assoc] at hh
    exact Int.ModEq.mul_right_cancel' (ne_of_gt hw) hh
  · rintro ⟨he,h⟩
    rw [he]
    have hh := (h.mul_right' (c:=w)).add_right t
    simpa only [mul_assoc] using hh

def gridIndex {G v : ℕ} (hG : 0<G) (hv : 0<v) (J : ℕ)
    (x : Fin G × Offsets J) : Fin (G*v) :=
  residue (Nat.mul_pos hG hv) ((x.1.val:ℤ)*v+x.2.val)

theorem gridIndex_injective {G v J : ℕ} (hG : 0<G) (hv : 0<v) (hJ : 2*J<v) :
    Function.Injective (gridIndex hG hv J) := by
  intro x y he
  have hm := (residue_eq_iff (Nat.mul_pos hG hv) _ _).mp he
  have ht : |x.2.val|≤(J:ℤ) := abs_le.mpr (Finset.mem_Icc.mp x.2.property)
  have ht' : |y.2.val|≤(J:ℤ) := abs_le.mpr (Finset.mem_Icc.mp y.2.property)
  have hsmall : (2:ℤ)*J<v := by exact_mod_cast hJ
  have hvm : (0:ℤ)<v := by exact_mod_cast hv
  have hdiv : (v:ℤ)∣(G*v:ℕ) := by exact_mod_cast dvd_mul_left v G
  have hoff : Int.ModEq v x.2.val y.2.val := by
    have hh := hm.of_dvd hdiv
    simpa [Int.ModEq] using hh
  have hxy : x.2.val=y.2.val := by
    apply equal_of_close_modEq hvm hoff
    have hh := abs_sub y.2.val x.2.val
    omega
  have hmain : Int.ModEq ((G:ℤ)*v) ((x.1.val:ℤ)*v) ((y.1.val:ℤ)*v) := by
    rw [hxy] at hm
    simpa only [Nat.cast_mul] using hm.add_right_cancel' y.2.val
  have hlabels := Int.ModEq.mul_right_cancel' (ne_of_gt hvm) hmain
  have hxG : (x.1.val:ℤ)<G := by exact_mod_cast x.1.isLt
  have hyG : (y.1.val:ℤ)<G := by exact_mod_cast y.1.isLt
  have hlab : (x.1.val:ℤ)=(y.1.val:ℤ) := by
    simpa only [Int.ModEq,Int.emod_eq_of_lt (by omega : (0:ℤ)≤x.1.val) hxG,
      Int.emod_eq_of_lt (by omega : (0:ℤ)≤y.1.val) hyG] using hlabels
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hlab
  · exact Subtype.ext hxy

#print axioms offset_separation
#print axioms gridIndex_injective

end GridCarrier
