module

public import AsymptoticNeumannReconstructionV1
public import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstruction

open ContinuousLinearMap Filter
open scoped Topology

variable {G E : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A finite polynomial in the actual low-height operator. -/
noncomputable def finiteLow (K : E →L[ℂ] E) (B : G →L[ℂ] E) (n : ℕ) : G →L[ℂ] E :=
  (∑ j∈Finset.range n,K^j).comp B

omit [NormedAddCommGroup G] [InnerProductSpace ℂ G] in
theorem power_norm_le (K : E →L[ℂ] E) {r : ℝ} (hK : ‖K‖≤r) (n : ℕ) : ‖K^n‖≤r^n := by
  have hr := (norm_nonneg K).trans hK
  induction n with
  | zero =>
    rw [pow_zero,pow_zero]
    exact norm_id_le
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih hK (norm_nonneg K) (pow_nonneg hr n))

/-- Finite Neumann sums obey the same reconstruction bound as the full
series; this preserves the common Fourier majorant during approximation. -/
theorem finiteLow_norm_le (K : E →L[ℂ] E) (B : G →L[ℂ] E) {r : ℝ}
    (hK : ‖K‖≤r) (hr : r<1) (n : ℕ) : ‖finiteLow K B n‖≤‖B‖/(1-r) := by
  have hr0 := (norm_nonneg K).trans hK
  have hs := summable_geometric_of_lt_one hr0 hr
  have hp : ‖∑ j∈Finset.range n,K^j‖≤(1-r)⁻¹ := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun j _ => power_norm_le K hK j)).trans
    apply (Summable.sum_le_tsum (Finset.range n) (fun j _ => pow_nonneg hr0 j) hs).trans_eq
    exact tsum_geometric_of_lt_one hr0 hr
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hp (norm_nonneg B)).trans_eq
  rw [div_eq_mul_inv,mul_comm]

theorem finiteLow_error [CompleteSpace E] (K : E →L[ℂ] E) (B : G →L[ℂ] E)
    {r C : ℝ} (hK : ‖K‖≤r) (hr : r<1) (hB : ‖B‖≤C) (n : ℕ) :
    ‖finiteLow K B n-low K B‖≤C*r^n/(1-r) := by
  have hr0 := (norm_nonneg K).trans hK
  have hs := summable_geometric_of_norm_lt_one (hK.trans_lt hr)
  have he : ‖(∑ j∈Finset.range n,K^j)-(∑' j : ℕ,K^j)‖≤r^n/(1-r) := by
    simpa only [one_mul] using norm_sub_le_of_geometric_bound_of_hasSum (C:=1) hr
      (fun j => by simpa only [one_mul] using power_norm_le K hK j) hs.hasSum n
  rw [finiteLow,low,← sub_comp]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul he hB (norm_nonneg B) (div_nonneg (pow_nonneg hr0 n) (sub_pos.mpr hr).le)).trans_eq
  ring

/-- Every finite-depth approximation has zero terminal output when the
actual low operator and terminal forcing have zero terminal output. -/
theorem finiteLow_terminal_zero (P K : E →L[ℂ] E) (B : G →L[ℂ] E)
    (hPK : ∀ x,P (K x)=0) (hPB : ∀ g,P (B g)=0) (n : ℕ) (g : G) :
    P (finiteLow K B n g)=0 := by
  have hp (j : ℕ) : P ((K^j) (B g))=0 := by
    cases j with
    | zero =>
      rw [pow_zero]
      exact hPB g
    | succ j =>
      rw [pow_succ']
      exact hPK ((K^j) (B g))
  change P ((∑ j∈Finset.range n,K^j) (B g))=0
  rw [sum_apply,map_sum]
  exact Finset.sum_eq_zero (fun j _ => hp j)

/-- A common contraction and forcing bound give a single finite depth
for an entire family, before varying weight or orbit root. -/
theorem finiteLow_tendstoUniformly [CompleteSpace E] {α : Type*}
    (K : α → E →L[ℂ] E) (B : α → G →L[ℂ] E) {r C : ℝ}
    (hr0 : 0≤r) (hr : r<1) (hK : ∀ a,‖K a‖≤r) (hB : ∀ a,‖B a‖≤C) :
    TendstoUniformly (fun n a => finiteLow (K a) (B a) n) (fun a => low (K a) (B a)) atTop := by
  have hd : Tendsto (fun n : ℕ => C*r^n/(1-r)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).const_mul C).div_const (1-r)
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  apply ((tendsto_order.mp hd).2 δ hδ).mono
  intro n hn a
  rw [dist_eq_norm,norm_sub_rev]
  exact (finiteLow_error (K a) (B a) (hK a) hr (hB a) n).trans_lt hn

#print axioms power_norm_le
#print axioms finiteLow_norm_le
#print axioms finiteLow_error
#print axioms finiteLow_terminal_zero
#print axioms finiteLow_tendstoUniformly

end AsymptoticReconstruction
