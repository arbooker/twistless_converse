module
public import QuantitativeArithmeticSmallLevelTwentySevenSourceCoverageV1
public import QuantitativeArithmeticSmallLevelTwentySevenBasisOriginalV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point physicalRow originalVector)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues)

inductive Kind where
  | hecke (j : ℕ) (valid : j∈QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.indices) : Kind
  | ramanujan (j : Fin 192) : Kind
  | matrix (j : Fin 119) : Kind
  | entire (j : Fin 8) : Kind

def source : Kind → ℕ
  | .hecke j _ => j
  | .ramanujan j => (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j).source
  | .matrix j => (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected j).source
  | .entire j => QuantitativeArithmeticSmallLevelTwentySevenEntireSource.source j

theorem source_exists (i : Fin 550) : ∃ r : Kind, source r=i.val := by
  rcases QuantitativeArithmeticSmallLevelTwentySevenSourceCoverage.coverage i with h|h|h|h
  · exact ⟨.hecke i.val h,rfl⟩
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp h
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
    refine ⟨.ramanujan (Fin.cast QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.specs_length j),?_⟩
    change (QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.specs.get j).source=i.val
    rw [hj]
    exact he
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp h
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
    refine ⟨.matrix (Fin.cast QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.specs_length j),?_⟩
    change (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.specs.get j).source=i.val
    rw [hj]
    exact he
  · obtain ⟨j,_,he⟩ := List.mem_map.mp h
    exact ⟨.entire j,he⟩

def kind (i : Fin 550) : Kind := Classical.choose (source_exists i)
theorem kind_source (i : Fin 550) : source (kind i)=i.val := Classical.choose_spec (source_exists i)

def row (r : Kind) (m : ℕ) (f : ℕ → ℂ) (η s : ℂ) : ℂ :=
  match r with
  | .hecke j _ => physicalRow point j m f s
  | .ramanujan j => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected j) m η s (fun n => SmallLevelAdditive.original (2*m) f (point n:ℝ) s)
  | .matrix j => QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.leading (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected j) m s (fun n => SmallLevelAdditive.original (2*m) f (point n:ℝ) s)
  | .entire j => physicalRow point (QuantitativeArithmeticSmallLevelTwentySevenEntireSource.source j) m f s

theorem row_one (r : Kind) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    row r m f 1 s=physicalRow point (source r) m f s := by
  cases r with
  | hecke j h => rfl
  | ramanujan j => exact (QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.selected_physical _ m f s).symm
  | matrix j => exact (QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.selected_physical _ m f s).symm
  | entire j => rfl

def originalRows (m : ℕ) (f : ℕ → ℂ) (η s : ℂ) : Fin 550 → ℂ :=
  fun i => row (kind i) m f η s

theorem originalRows_one (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    originalRows m f 1 s=physicalSource m ((Real.sqrt 2:ℂ)*f 2)
      ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7) s *ᵥ originalVector m f s := by
  funext i
  rw [QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.source_action]
  change row (kind i) m f 1 s=physicalRow point i.val m f s
  rw [row_one,kind_source]

#print axioms source_exists
#print axioms row_one
#print axioms originalRows_one
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
