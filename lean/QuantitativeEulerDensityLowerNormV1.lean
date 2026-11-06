module

public import QuantitativeEulerDensityIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open AsymptoticCongruenceLabels QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- The actual signed lower-unipotent telescope has exactly |r| terms.
Every transported observation has an explicit matrix height bounded by
2(1+N|r|)B. In particular no choice of a word or a height depending
unquantifiably on r enters this compact norm estimate. -/
theorem lower_power_compact_norm (N : ℕ) (r : ℤ) :
    ∃ (n : ℕ) (e : ℕ → ℤ), n=r.natAbs ∧ (∀ j<n, |e j|≤|r|) ∧
    ∀ (β : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s) {B H ε : ℝ}
      (_hB : 0≤B) (_hb : MatrixEntryBound β.val B) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    ‖matrixCompactAction hs hε t x
      ((matrixSymbol (lowerUnipotent N r)-1)*matrixSymbol β.val) v‖≤
      (integerCompactDistortion (2*(1+(N : ℝ)*|(r : ℝ)|)*B) H)^t*
        ∑ j∈Finset.range n, ‖AsymptoticCongruenceDefect.operator (lowerSL N 1)
          (branchImage_compact (symbolBranch (integralLabel (lowerSL N (e j)*β))) hs) hε t x v‖ := by
  obtain ⟨n,sgn,e,hn,hsign,he,hid⟩ := lower_defect_signed_sum N r
  refine ⟨n,e,hn,he,?_⟩
  intro β s hs B H ε hB hb hε hre him t x v
  have hop : matrixCompactAction hs hε t x
      ((matrixSymbol (lowerUnipotent N r)-1)*matrixSymbol β.val)=
      sgn • ∑ j∈Finset.range n, matrixCompactAction hs hε t x
        ((matrixSymbol (lowerSL N 1).val-1)*matrixSymbol (lowerSL N (e j)*β).val) := by
    rw [hid,smul_mul_assoc,map_zsmul,Finset.sum_mul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc,←matrixSymbol_mul]
    rfl
  have hnorm : ‖matrixCompactAction hs hε t x
      ((matrixSymbol (lowerUnipotent N r)-1)*matrixSymbol β.val) v‖≤
      ∑ j∈Finset.range n, ‖matrixCompactAction hs hε t x
        ((matrixSymbol (lowerSL N 1).val-1)*matrixSymbol (lowerSL N (e j)*β).val) v‖ := by
    rw [hop]
    rcases hsign with hh | hh
    · rw [hh,one_smul,_root_.sum_apply]
      exact norm_sum_le _ _
    · rw [hh,neg_one_smul,_root_.neg_apply,norm_neg,_root_.sum_apply]
      exact norm_sum_le _ _
  apply hnorm.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hej : |((e j) : ℝ)|≤|(r : ℝ)| := by
    exact_mod_cast he j (Finset.mem_range.mp hj)
  have hV : MatrixEntryBound (lowerSL N (e j)).val (1+(N : ℝ)*|(r : ℝ)|) := by
    intro a b
    have h := lowerUnipotent_entry_bound (N : ℤ) (e j) a b
    change |((lowerUnipotent N (e j) a b : ℤ) : ℝ)|≤_
    apply h.trans
    simp only [Int.cast_natCast,Nat.abs_cast]
    gcongr
  have hprod : MatrixEntryBound (lowerSL N (e j)*β).val
      (2*(1+(N : ℝ)*|(r : ℝ)|)*B) :=
    matrix_entry_bound_mul (by positivity) hV hb
  exact matrixCompactAction_integral_defect_norm (lowerSL N 1) (lowerSL N (e j)*β)
    hs (by positivity) hprod hε hre him t x v

#print axioms lower_power_compact_norm
end QuantitativeEulerDensityGenerators
