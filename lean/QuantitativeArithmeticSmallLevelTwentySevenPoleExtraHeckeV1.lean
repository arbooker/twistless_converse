module
public import QuantitativeArithmeticSmallLevelTwentySevenSourceDispatchTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource
open QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch (physicalEval)
def heckePoly : Fin 17 → QuantitativeArithmeticSevenLaurentRows.Poly := ![extraPoly3,extraPoly4,extraPoly5,extraPoly6,extraPoly7,extraPoly8,extraPoly9,extraPoly12,extraPoly13,extraPoly14,extraPoly15,extraPoly16,extraPoly17,extraPoly18,extraPoly19,extraPoly20,extraPoly21]
theorem hecke_original (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ i : Fin 17, ∀ s : ℂ, B<s.re → physicalEval (heckePoly i) m f s=0 := by
  have hi (i : Fin 17) : ∃ B : ℝ, ∀ s : ℂ, B<s.re → physicalEval (heckePoly i) m f s=0 := by
    fin_cases i
    · exact extraOriginal3 hm hf
    · exact extraOriginal4 hm hf
    · exact extraOriginal5 hm hf
    · exact extraOriginal6 hm hf
    · exact extraOriginal7 hm hf
    · exact extraOriginal8 hm hf
    · exact extraOriginal9 hm hf
    · exact extraOriginal12 hm hf
    · exact extraOriginal13 hm hf
    · exact extraOriginal14 hm hf
    · exact extraOriginal15 hm hf
    · exact extraOriginal16 hm hf
    · exact extraOriginal17 hm hf
    · exact extraOriginal18 hm hf
    · exact extraOriginal19 hm hf
    · exact extraOriginal20 hm hf
    · exact extraOriginal21 hm hf
  choose b hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  refine ⟨B,?_⟩
  intro i s hs
  exact hb i s (lt_of_le_of_lt (Finset.le_sup' b (Finset.mem_univ i)) hs)
#print axioms hecke_original
end QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource
