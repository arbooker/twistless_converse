module
public import QuantitativeArithmeticSmallLevelTwentySevenShiftFactorsV1
public import QuantitativeArithmeticSmallLevelTwentySevenSourceActionV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenShiftSource
open _root_.Matrix QuantitativeArithmeticRationalRows
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point originalVector)

private theorem basis_support_check :
    (List.range 321).all (fun i => (basis i).all (fun t => decide (t.2<607)))=true := by
  decide +kernel

theorem basis_support (i : Fin 321) : ∀ t∈basis i.val, t.2<607 := by
  intro t ht
  have hi := List.all_eq_true.mp basis_support_check i.val (List.mem_range.mpr i.isLt)
  exact of_decide_eq_true (List.all_eq_true.mp hi t ht)

theorem basisValues_original (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    basisValues (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)=
      basisMatrix *ᵥ originalVector m f s := by
  funext i
  exact eval_bounded_eq_sum _ _ (basis_support i)

/-- The original 321 observations are holomorphic on one common initial
half-plane, before any continuation is performed. -/
theorem original_basis_analytic (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ i : Fin 321, ∀ s : ℂ, B<s.re →
      AnalyticAt ℂ (fun z => (basisMatrix *ᵥ originalVector m f z) i) s := by
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,?_⟩
  intro i s hs
  change AnalyticAt ℂ (fun z => ∑ j : Fin 607, basisMatrix i j*originalVector m f z j) s
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul ((hB (point j.val) s hs).1)
#print axioms basis_support
#print axioms basisValues_original
#print axioms original_basis_analytic
end QuantitativeArithmeticSmallLevelTwentySevenShiftSource
