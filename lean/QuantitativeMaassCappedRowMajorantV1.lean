module

public import QuantitativeMaassCappedRowBoundV1
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticCompactBranch
open scoped MatrixGroups

namespace QuantitativeMaass

def integerSquareTail (n : ℤ) : ℝ := if n=0 then 1 else 1/(n:ℝ)^2

theorem integerSquareTail_nonneg (n : ℤ) : 0 ≤ integerSquareTail n := by
  unfold integerSquareTail
  split_ifs <;> positivity

theorem integerSquareTail_summable : Summable integerSquareTail := by
  have hs : Summable (fun n : ℤ => if n=0 then (1:ℝ) else 0) :=
    summable_of_hasFiniteSupport (by simp [Function.HasFiniteSupport,Function.support])
  have ht := hs.add (Real.summable_one_div_int_pow.mpr (by norm_num : 1<2))
  apply ht.congr
  intro n
  by_cases hn : n=0 <;> simp [integerSquareTail,hn]

theorem integerSquareTail_dominates (n : ℤ) :
    1/(1+|(n:ℝ)|)^2 ≤ integerSquareTail n := by
  by_cases hn : n=0
  · simp [integerSquareTail,hn]
  · rw [integerSquareTail,ite_eq_right hn]
    apply one_div_le_one_div_of_le (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hn))
    nlinarith [sq_abs (n:ℝ),abs_nonneg (n:ℝ)]

def cappedRowMajorant (ε : ℝ) (a : ℤ × ℤ) : ℝ :=
  (1+16/ε^2)*integerSquareTail a.1*integerSquareTail a.2

theorem cappedRowMajorant_nonneg (ε : ℝ) (a : ℤ × ℤ) : 0 ≤ cappedRowMajorant ε a := by
  unfold cappedRowMajorant
  exact mul_nonneg (mul_nonneg (by positivity) (integerSquareTail_nonneg _))
    (integerSquareTail_nonneg _)

theorem cappedRowMajorant_summable (ε : ℝ) : Summable (cappedRowMajorant ε) := by
  have hs := integerSquareTail_summable.mul_of_nonneg integerSquareTail_summable
    integerSquareTail_nonneg integerSquareTail_nonneg
  change Summable (fun a : ℤ × ℤ => (1+16/ε^2)*integerSquareTail a.1*integerSquareTail a.2)
  simpa only [mul_assoc] using hs.mul_left (1+16/ε^2)

theorem cap_le_first_power {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1 ≤ v) (z : ℍ) :
    cap ε v z ≤ min (z.im/ε) 1 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v≠0)
  unfold cap
  rw [pow_succ]
  have hn : 0 ≤ min (z.im/ε) 1 := le_min (div_pos z.im_pos hε).le zero_le_one
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hn (min_le_right _ _)) hn

/-- One summable majorant controls all primitive integral rows in the
standard cusp strip, at every positive integral cap exponent. -/
theorem cap_sq_le_cappedRowMajorant {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1 ≤ v)
    (A : SL(2,ℤ)) (z : ℍ) (hx : |z.re| ≤ 1/2) (hy : 1/2 ≤ z.im) :
    cap ε v (A•z)^2 ≤ cappedRowMajorant ε (A.val 1 0,A.val 1 1) := by
  have hcap := cap_le_first_power hε hv (A•z)
  by_cases hc : A.val 1 0=0
  · have hdet := A.property
    rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hdet
    have hd : A.val 1 1=1 ∨ A.val 1 1=-1 :=
      Int.eq_one_or_neg_one_of_mul_eq_one (by simpa only [mul_comm] using hdet)
    have hb : cap ε v (A•z)^2 ≤ 1 := by
      have hle := hcap.trans (min_le_right _ _)
      nlinarith [cap_pos hε v (A•z)]
    have hle : cap ε v (A•z)^2 ≤ 1+16/ε^2 :=
      hb.trans (le_add_of_nonneg_right (by positivity))
    rcases hd with hd | hd <;>
      simpa only [cappedRowMajorant,integerSquareTail,hc,hd,ite_true,
        show (1:ℤ)≠0 by norm_num, show (-1:ℤ)≠0 by norm_num,
        ite_false,Int.cast_one,Int.cast_neg,neg_sq,one_pow,div_one,mul_one] using hle
  · have hc' : 1 ≤  |(A.val 1 0:ℝ)| := by
      have hp : (0:ℤ)< |A.val 1 0| := abs_pos.mpr hc
      exact_mod_cast (show (1:ℤ) ≤ |A.val 1 0| by omega)
    have hb := cusp_row_height_square_bound (A.val 1 0) (A.val 1 1) z.re z.im hc' hx hy
    have hheight : (A•z).im=z.im/(((A.val 1 0:ℝ)*z.re+(A.val 1 1:ℝ))^2+
        ((A.val 1 0:ℝ)*z.im)^2) := by
      rw [ModularGroup.im_smul_eq_div_normSq,ModularGroup.denom_apply]
      congr 1
      simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
      ring
    rw [←hheight] at hb
    have hs : cap ε v (A•z)^2 ≤ (A•z).im^2/ε^2 := by
      have hh := pow_le_pow_left₀ (cap_pos hε v (A•z)).le (hcap.trans (min_le_left _ _)) 2
      simpa only [div_pow] using hh
    have htail := integerSquareTail_dominates (A.val 1 1)
    have hct : integerSquareTail (A.val 1 0)=1/(A.val 1 0:ℝ)^2 := by
      simp only [integerSquareTail,ite_eq_right hc]
    calc
      _ ≤ (A•z).im^2/ε^2 := hs
      _ ≤ (16/((A.val 1 0:ℝ)^2*(1+|(A.val 1 1:ℝ)|)^2))/ε^2 :=
        div_le_div_of_nonneg_right hb (sq_nonneg ε)
      _=(16/ε^2)*integerSquareTail (A.val 1 0)*(1/(1+|(A.val 1 1:ℝ)|)^2) := by
        rw [hct]
        simp only [div_eq_mul_inv,_root_.mul_inv_rev]
        ring
      _ ≤ (16/ε^2)*integerSquareTail (A.val 1 0)*integerSquareTail (A.val 1 1) :=
        mul_le_mul_of_nonneg_left htail (mul_nonneg (by positivity) (integerSquareTail_nonneg _))
      _ ≤ cappedRowMajorant ε (A.val 1 0,A.val 1 1) := by
        unfold cappedRowMajorant
        nlinarith [mul_nonneg (integerSquareTail_nonneg (A.val 1 0))
          (integerSquareTail_nonneg (A.val 1 1))]

#print axioms integerSquareTail_nonneg
#print axioms integerSquareTail_summable
#print axioms integerSquareTail_dominates
#print axioms cappedRowMajorant_nonneg
#print axioms cappedRowMajorant_summable
#print axioms cap_le_first_power
#print axioms cap_sq_le_cappedRowMajorant

end QuantitativeMaass
