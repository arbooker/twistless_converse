module

public import QuantitativeNewGapTreeSchurV1

set_option autoImplicit false
@[expose] public noncomputable section

open QuantitativeMaass
open scoped BigOperators lp

namespace QuantitativeNewGap

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Positive radial edge-of-spectrum Schur weight. Its linear factor is
chosen so that the root has the same weighted degree as every other vertex. -/
def treeSchurWeight (r : ℝ) (v : TreeWord α) : ℝ :=
  (1+(r^2-1)/(r^2+1)*(v.val.length:ℝ))*(r⁻¹)^v.val.length

omit [Fintype α] [DecidableEq α] in
theorem treeSchurWeight_pos {r : ℝ} (hr : 1<r) (v : TreeWord α) :
    0<treeSchurWeight r v := by
  have hnum : 0<r^2-1 := by nlinarith
  dsimp [treeSchurWeight]
  positivity

theorem treeSchurWeight_equation {r : ℝ} (hr : 1<r)
    (hd : (Fintype.card α:ℝ)=r^2+1) (v : TreeWord α) :
    (∑ a : α,treeSchurWeight r (TreeWord.step a v))=2*r*treeSchurWeight r v := by
  have hr0 : r≠0 := ne_of_gt (lt_trans zero_lt_one hr)
  have hden : r^2+1≠0 := by positivity
  rcases v with ⟨l,hl⟩
  cases l with
  | nil =>
    simp only [treeSchurWeight,TreeWord.step,TreeWord.stepList,List.length_singleton,
      Nat.cast_one,pow_one,List.length_nil,Nat.cast_zero,mul_zero,add_zero,pow_zero,mul_one,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [hd]
    field_simp
    ring
  | cons b l =>
    have hcard : 1≤Fintype.card α := Fintype.card_pos_iff.mpr ⟨b⟩
    have hc : ((Fintype.card α-1:ℕ):ℝ)=r^2 := by
      rw [Nat.cast_sub hcard,Nat.cast_one,hd]
      ring
    have hpoint (a : α) : treeSchurWeight r (TreeWord.step a ⟨b::l,hl⟩)=
        if a=b then (1+(r^2-1)/(r^2+1)*(l.length:ℝ))*(r⁻¹)^l.length
        else (1+(r^2-1)/(r^2+1)*((l.length+2:ℕ):ℝ))*(r⁻¹)^(l.length+2) := by
      by_cases hab : a=b <;> simp [TreeWord.step,TreeWord.stepList,treeSchurWeight,hab,add_assoc]
    simp_rw [hpoint]
    rw [Finset.sum_ite]
    have heq : Finset.univ.filter (fun a : α => a=b)={b} := by ext a; simp
    rw [heq]
    simp only [Finset.sum_const,Finset.filter_ne',Finset.card_singleton,Finset.card_univ,
      Finset.card_erase_of_mem (Finset.mem_univ b),nsmul_eq_mul,hc,
      treeSchurWeight,List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    simp only [pow_succ,pow_zero]
    field_simp [hr0,hden]
    ring

/-- The sharp global norm bound for the actual colored-tree adjacency,
proved on the entire counting Hilbert space, not merely at the root. -/
theorem treeAdjacency_sharp_norm_le {p : ℝ} (hp : 1<p)
    (hcard : (Fintype.card α:ℝ)=p+1) :
    ‖treeAdjacency (α:=α)‖≤2*Real.sqrt p := by
  have hr : 1<Real.sqrt p := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) hp
  have hd : (Fintype.card α:ℝ)=(Real.sqrt p)^2+1 := by
    rw [Real.sq_sqrt (lt_trans zero_lt_one hp).le,hcard]
  exact involution_sum_norm_le (fun a : α => TreeWord.edgeEquiv a)
    TreeWord.step_involutive (treeSchurWeight (Real.sqrt p))
    (treeSchurWeight_pos hr) (2*Real.sqrt p) (by positivity)
    (treeSchurWeight_equation hr hd)

/-- The neighbor average is a strict contraction for p>1. This is the
regular-tree angle bound; no physical cuspidal Satake estimate is asserted. -/
theorem tree_neighbor_average_norm_lt_one {p : ℝ} (hp : 1<p)
    (hcard : (Fintype.card α:ℝ)=p+1) :
    ‖(p+1)⁻¹ • treeAdjacency (α:=α)‖≤2*Real.sqrt p/(p+1) ∧
      2*Real.sqrt p/(p+1)<1 := by
  have hp0 : 0<p := lt_trans zero_lt_one hp
  have hd : 0<p+1 := by positivity
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
    simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left (treeAdjacency_sharp_norm_le hp hcard) (inv_nonneg.mpr hd.le)
  · rw [div_lt_one hd]
    have hr : 1<Real.sqrt p := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) hp
    have hs := Real.sq_sqrt hp0.le
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]

#print axioms treeSchurWeight_equation
#print axioms treeAdjacency_sharp_norm_le
#print axioms tree_neighbor_average_norm_lt_one

end QuantitativeNewGap
