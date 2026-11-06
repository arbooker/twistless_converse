module
public import QuantitativeArithmeticSmallLevelTwentySevenObservationTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenRamanujanSourceTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenShiftSource
open QuantitativeArithmeticRationalRows
open QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource
open FinitenessRamanujanSum

def sampleRow (ids : List ℕ) (sample : ℕ → ℕ) : Row := ids.map (fun j => (1,sample j))

theorem eval_sampleRow (v : ℕ → ℂ) {q : ℕ} (ids : List ℕ) (sample : ℕ → ℕ)
    (hn : ids.Nodup) (hr : ids.toFinset=residues q) :
    eval v (sampleRow ids sample)=sampleEval q sample v := by
  simp only [eval,sampleRow,List.map_map,Rat.cast_one,one_mul,Function.comp_def]
  rw [← List.sum_toFinset _ hn,hr]
  rfl
#print axioms eval_sampleRow
end QuantitativeArithmeticSmallLevelTwentySevenShiftSource
