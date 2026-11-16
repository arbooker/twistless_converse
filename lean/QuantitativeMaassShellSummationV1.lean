module

public import QuantitativeMaassUnitShellCountV1
public import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass

/-- The fixed numerical mass used to sum spectral shells. -/
def cubicShellMass : ℝ := ∑' n : ℕ,1/((n:ℝ)+1)^3

theorem cubicShell_summable : Summable (fun n : ℕ => 1/((n:ℝ)+1)^3) := by
  have hh : Summable (fun n : ℕ => 1/(n:ℝ)^3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs := (summable_nat_add_iff 1).mpr hh
  simpa only [Nat.cast_add,Nat.cast_one] using hs

/-- Linear shell cardinalities and fourth-power pointwise decay give an
absolutely convergent weighted sum, with an explicit uniform constant. -/
theorem linear_shell_weight_sum {ι : Type*} (j : ι → ℕ) (f : ι → ℝ)
    (hf : ∀ i,0≤f i) (C A t : ℝ) (hC : 0≤C) (hA : 0≤A) (ht : 0≤t)
    (hfinite : ∀ n : ℕ,{i | j i=n}.Finite)
    (hcard : ∀ n : ℕ,(Nat.card {i // j i=n}:ℝ)≤C*(t+n+2))
    (hpoint : ∀ i,f i≤A/((j i:ℝ)+1)^4) :
    Summable f ∧ (∑' i,f i)≤C*(t+2)*A*cubicShellMass := by
  classical
  let S : ℕ → Set ι := fun n => {i | j i=n}
  let (n : ℕ) : Fintype (S n) := (hfinite n).fintype
  have hlocal (n : ℕ) : (∑' i : S n,f i.val)≤(C*(t+2)*A)/((n:ℝ)+1)^3 := by
    have hn : 0<(n:ℝ)+1 := by positivity
    have hnum : t+n+2≤(t+2)*((n:ℝ)+1) := by
      nlinarith [mul_nonneg ht (Nat.cast_nonneg n)]
    calc
      _ = ∑ i : S n,f i.val := tsum_fintype _
      _ ≤ ∑ _i : S n,A/((n:ℝ)+1)^4 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [show j i.val=n from i.property] using hpoint i.val
      _ = (Fintype.card (S n):ℝ)*(A/((n:ℝ)+1)^4) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (C*(t+n+2))*(A/((n:ℝ)+1)^4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcn : (Nat.card (S n):ℝ)≤C*(t+n+2) := hcard n
        simpa only [Nat.card_eq_fintype_card] using hcn
      _ ≤ (C*((t+2)*((n:ℝ)+1)))*(A/((n:ℝ)+1)^4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hC) (by positivity)
      _ = _ := by field_simp
  have hmajor : Summable (fun n : ℕ => (C*(t+2)*A)/((n:ℝ)+1)^3) := by
    simpa only [mul_one_div] using cubicShell_summable.mul_left (C*(t+2)*A)
  have houter : Summable (fun n : ℕ => ∑' i : S n,f i.val) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => hf i.val)) hlocal hmajor
  have hsum : Summable f := (summable_partition hf
    (s:=S) (fun i => ⟨j i,rfl,fun n hn => hn.symm⟩)).mpr
      ⟨fun n => (hasSum_fintype _).summable,houter⟩
  refine ⟨hsum,?_⟩
  have heq : (∑' n : ℕ,∑' i : S n,f i.val)=∑' i,f i :=
    (hsum.hasSum.tsum_fiberwise j).tsum_eq
  rw [←heq]
  calc
    _ ≤ ∑' n : ℕ,(C*(t+2)*A)/((n:ℝ)+1)^3 := houter.tsum_le_tsum hlocal hmajor
    _ = _ := by simp only [div_eq_mul_inv,tsum_mul_left,cubicShellMass,one_mul]

#print axioms cubicShell_summable
#print axioms linear_shell_weight_sum

end QuantitativeMaass
