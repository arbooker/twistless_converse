module

public import AsymptoticFoldTruncationV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteFoldAssembly

open Filter

variable {ι α E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A single finite fold set approximates a finite stack of branches,
uniformly over all parameters, including variable sector amplitudes. -/
theorem tendstoUniformly (f : ι → ℤ → α → E) (c : ι → α → ℂ)
    (b : ι → ℤ → ℝ) (hb : ∀ v,Summable (b v))
    (hf : ∀ v n a,‖c v a • f v n a‖≤b v n) :
    TendstoUniformly
      (fun I : Finset ℤ => fun a => ∑ v,c v a • ∑ n∈I,f v n a)
      (fun a => ∑ v,c v a • ∑' n,f v n a) atTop := by
  classical
  have hs (v : ι) (a : α) : Summable (fun n => c v a • f v n a) :=
    Summable.of_norm_bounded (hb v) (fun n => hf v n a)
  have hu : Summable (fun n => ∑ v,b v n) :=
    (hasSum_sum (fun v _ => (hb v).hasSum)).summable
  have h := tendstoUniformly_tsum hu (fun n a =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v _ => hf v n a)))
  have he (a : α) : (∑' n,∑ v,c v a • f v n a)=∑ v,c v a • ∑' n,f v n a := by
    rw [Summable.tsum_finsetSum (fun v _ => hs v a)]
    simp only [tsum_const_smul'']
  simp only [he] at h
  convert h using 1
  funext I a
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

omit [CompleteSpace E] in
/-- Truncation retains the same scalar majorant as the full certificate. -/
theorem norm_le (f : ι → E) (c : ι → ℂ) (b a : ι → ℝ)
    (hc : ∀ v,‖c v‖=a v) (hf : ∀ v,‖f v‖≤b v) :
    ‖∑ v,c v • f v‖≤∑ v,a v*b v := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,hc]
  exact mul_le_mul_of_nonneg_left (hf v) ((hc v) ▸ norm_nonneg (c v))

#print axioms tendstoUniformly
#print axioms norm_le

end AsymptoticFiniteFoldAssembly
