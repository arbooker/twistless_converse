module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridRowModelV1
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

/-- The original physical rows together with coordinates of the already
continued 150-grid. The gauge-coordinate equations are added separately. -/
inductive SourceRow where
  | physical : Row → SourceRow
  | old : Fin 150 → SourceRow

def sourceLeading (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (v : Fin 1050 → ℂ) : ℂ :=
  match r with
  | .physical r => leading r m f ε s v
  | .old j => v ⟨7*j.val,by omega⟩

def sourceShifted (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 1050 → ℂ) : ℂ :=
  match r with
  | .physical r => shifted r m f ε n s v
  | .old _ => 0

end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
