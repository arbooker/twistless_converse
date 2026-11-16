module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {H I : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Contractive factors give a contractive ordered product, including
the empty product on a possibly trivial space. -/
theorem operator_list_product_contraction (A : I→H→L[ℂ]H)
    (hA : ∀ i,‖A i‖≤1) (L : List I) : ‖(L.map A).prod‖≤1 := by
  induction L with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons i L ih =>
    simp only [List.map_cons,List.prod_cons]
    exact (norm_mul_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul (hA i) ih (norm_nonneg _) zero_le_one)

/-- Telescoping ordered products does not require the approximate
factors to commute. A fixed factor two allows approximation errors. -/
theorem operator_list_product_difference (A B : I→H→L[ℂ]H)
    (hA : ∀ i,‖A i‖≤2) (hB : ∀ i,‖B i‖≤1) (L : List I) :
    ‖(L.map A).prod-(L.map B).prod‖ ≤
      (2:ℝ)^L.length*(L.map (fun i => ‖A i-B i‖)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,List.length_cons]
    have he : A i*(L.map A).prod-B i*(L.map B).prod=
        A i*((L.map A).prod-(L.map B).prod)+(A i-B i)*(L.map B).prod := by noncomm_ring
    rw [he]
    have hb := operator_list_product_contraction B hB L
    have ht := (norm_add_le (A i*((L.map A).prod-(L.map B).prod))
      ((A i-B i)*(L.map B).prod)).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    have hx := mul_le_mul (hA i) ih (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
    have hy := mul_le_mul_of_nonneg_left hb (norm_nonneg (A i-B i))
    have hs : 0≤(L.map (fun j => ‖A j-B j‖)).sum :=
      List.sum_nonneg (fun x hx => by obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
    have hp : 1≤(2:ℝ)^L.length := one_le_pow₀ (by norm_num)
    rw [pow_succ']
    nlinarith only [ht,hx,hy,hp,hs,norm_nonneg (A i-B i)]

#print axioms operator_list_product_contraction
#print axioms operator_list_product_difference
end QuantitativeMaass
