module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public section

namespace AsymptoticBlockLoss

open Filter
open scoped Topology

/-- The finite-block calculation with the paper's exact denominator.
`r` is the original individual rank, `s` the restricted rank, and `d`
the trace removed by each averaged equation. -/
theorem block_loss {m : ℕ} (hm : 0<m) (e qmax : ℝ)
    (q r s d : Fin m → ℝ) (hd : ∀ i,0≤d i) (hq : 1<qmax)
    (hmax : ∀ i,q i≤qmax) (hdetect : e≤∑ i,r i)
    (hrestrict : ∀ i,r i≤s i+((∑ j,d j)-d i))
    (hfresh : ∀ i,s i≤(q i-1)*d i) :
    e/(qmax+(m:ℝ)-2)≤∑ i,d i := by
  have hden : 0<qmax+(m:ℝ)-2 := by
    have hm' : (1:ℝ)≤m := by exact_mod_cast hm
    linarith
  have hstep (i : Fin m) : r i≤(qmax-2)*d i+∑ j,d j := by
    have hb := mul_le_mul_of_nonneg_right (sub_le_sub_right (hmax i) 1) (hd i)
    linarith [hrestrict i,hfresh i]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hstep i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem block_excess {m : ℕ} (hm : 0<m) (e qmax : ℝ)
    (q r s d : Fin m → ℝ) (hd : ∀ i,0≤d i) (hq : 1<qmax)
    (hmax : ∀ i,q i≤qmax) (hdetect : e≤∑ i,r i)
    (hrestrict : ∀ i,r i≤s i+((∑ j,d j)-d i))
    (hfresh : ∀ i,s i≤(q i-1)*d i) :
    e-(∑ i,d i)≤(1-1/(qmax+(m:ℝ)-2))*e := by
  have h := block_loss hm e qmax q r s d hd hq hmax hdetect hrestrict hfresh
  rw [div_eq_mul_inv] at h ⊢
  nlinarith

/-- Repeated proportional loss has an explicit exponential bound.
The arithmetic construction of loss parameters is a separate input. -/
theorem excess_le_exp (e a : ℕ → ℝ) (he : ∀ n,0≤e n)
    (hstep : ∀ n,e (n+1)≤(1-a n)*e n) (n : ℕ) :
    e n≤e 0*Real.exp (-(∑ i∈Finset.range n,a i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : 1-a n≤Real.exp (-a n) := by
      simpa only [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-a n)
    calc
      e (n+1)≤(1-a n)*e n := hstep n
      _≤Real.exp (-a n)*e n := mul_le_mul_of_nonneg_right hc (he n)
      _≤Real.exp (-a n)*(e 0*Real.exp (-(∑ i∈Finset.range n,a i))) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
      _=e 0*Real.exp (-(∑ i∈Finset.range (n+1),a i)) := by
        rw [Finset.sum_range_succ,neg_add,Real.exp_add]
        ring

/-- Divergence of the sum of actual block-loss parameters forces the
regular excess to zero. This does not postulate prime distribution. -/
theorem excess_tendsto_zero (e a : ℕ → ℝ) (he : ∀ n,0≤e n)
    (hstep : ∀ n,e (n+1)≤(1-a n)*e n)
    (hdiv : Tendsto (fun n => ∑ i∈Finset.range n,a i) atTop atTop) :
    Tendsto e atTop (𝓝 0) := by
  have ht := (tendsto_const_nhds (x:=e 0)).mul
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv)
  have ht' : Tendsto (fun n => e 0*Real.exp (-(∑ i∈Finset.range n,a i))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using ht
  exact squeeze_zero he (excess_le_exp e a he hstep) ht'

#print axioms block_loss
#print axioms block_excess
#print axioms excess_le_exp
#print axioms excess_tendsto_zero

/-- A persistent positive defect rank cannot survive infinitely many
fresh equations whose loss parameters have divergent sum. Unlike the
block argument, this only needs a finite trace budget and can be applied
to each generator separately; the invariant part may shrink as well. -/
theorem persistent_rank_zero (p a : ℕ → ℝ) (r : ℝ)
    (hp : ∀ n,0≤p n) (hr : 0≤r)
    (hstep : ∀ n,r*a n≤p n-p (n+1))
    (hdiv : Tendsto (fun n => ∑ i∈Finset.range n,a i) atTop atTop) : r=0 := by
  have hbudget (n : ℕ) : r*(∑ i∈Finset.range n,a i)+p n≤p 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,mul_add]
      linarith [hstep n]
  by_contra hn
  have hr' : 0<r := lt_of_le_of_ne hr (Ne.symm hn)
  obtain ⟨n,hn⟩ := ((tendsto_atTop.1 hdiv) (p 0/r+1)).exists
  have hm := mul_le_mul_of_nonneg_left hn hr
  have he : r*(p 0/r+1)=p 0+r := by field_simp
  rw [he] at hm
  linarith [hbudget n,hp n]

#print axioms persistent_rank_zero

end AsymptoticBlockLoss
