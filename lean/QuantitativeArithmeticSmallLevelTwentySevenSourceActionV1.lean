module
public import QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
open Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

private theorem source_support_check :
    (List.range 550).all (fun i => (inputs i).all (fun t => decide (t.2.1<607)))=true := by
  decide +kernel

theorem source_support (i : Fin 550) : ∀ t∈inputs i.val, t.2.1<607 := by
  have hi := List.all_eq_true.mp source_support_check i.val (List.mem_range.mpr i.isLt)
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp hi t ht)

def originalVector (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin 607 → ℂ :=
  fun j => SmallLevelAdditive.original (2*m) f (point j.val:ℝ) s

theorem source_action (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 550) :
    (physicalSource m ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5)
      ((Real.sqrt 7:ℂ)*f 7) s *ᵥ originalVector m f s) i = physicalRow point i.val m f s := by
  simpa only [physicalSource,sourceMatrix,physicalRow,originalVector,Matrix.mulVec,dotProduct] using
    (eval_bounded_eq_sum (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7)
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s) (inputs i.val)
      (source_support i)).symm

/-- The selected Hecke equations are zero coordinates of the literal
550 by 607 source matrix acting on the original additive transforms. -/
theorem original_hecke_source_action {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i : Fin 550, i.val∈indices →
      (physicalSource m ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5)
        ((Real.sqrt 7:ℂ)*f 7) s *ᵥ originalVector m f s) i=0 := by
  obtain ⟨B,hB⟩ := original_hecke_sources hm hf
  refine ⟨B,?_⟩
  intro s hs i hi
  rw [source_action]
  exact hB s hs i.val hi
#print axioms source_support
#print axioms original_hecke_source_action
end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
