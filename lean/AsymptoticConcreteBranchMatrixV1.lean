module

public import AsymptoticConcreteBranchAdjointV1
public import AsymptoticRationalCompactFoldV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticConcreteRationalBranch

open UpperHalfPlane MeasureTheory Filter
open AsymptoticRationalFreeness AsymptoticRationalBranches AsymptoticSlashGauge

/-- The chosen representative in the projective implementation gives
exactly the original rational matrix slash operator in even weight. -/
theorem operator_ofMatrix (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (a : ℍ → ℂ) (hm : Measurable a) {C : ℝ} (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    operator (ofMatrix g hg) a hm ha m=
      (AsymptoticL2Multiplier.operator a hm.aestronglyMeasurable (Eventually.of_forall ha)).comp
        (AsymptoticHyperbolicSlash.operator (realMatrix g) (2*m)) := by
  have he : Matrix.ProjGenLinGroup.mk (realMatrix (representative (ofMatrix g hg)))=
      Matrix.ProjGenLinGroup.mk (realMatrix g) := by
    change AsymptoticRationalGroup.rationalMap (representative (ofMatrix g hg))=
      AsymptoticRationalGroup.rationalMap g
    rw [representative_spec]
    rfl
  rw [operator,AsymptoticHyperbolicSlash.operator_projective_eq he m]

theorem operator_fold {L : ℚ} (hL : 0<L) (b d : ℚ) (n : ℤ)
    (a : ℍ → ℂ) (hm : Measurable a) {C : ℝ} (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    operator (AsymptoticRationalBranches.fold hL b d n) a hm ha m=
      (AsymptoticL2Multiplier.operator a hm.aestronglyMeasurable (Eventually.of_forall ha)).comp
        (AsymptoticHyperbolicSlash.operator
          (AsymptoticFoldedLow.fold (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) n) (2*m)) := by
  rw [AsymptoticRationalBranches.fold,operator_ofMatrix,realMatrix_branch]
  simp only [Rat.cast_sub,Rat.cast_intCast,AsymptoticFoldedLow.fold]

theorem operator_compactFold (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val) (n : ℤ)
    (a : ℍ → ℂ) (hm : Measurable a) {C : ℝ} (ha : ∀ z,‖a z‖≤C) (m : ℕ) :
    operator (compactFold g hg n) a hm ha m=
      (AsymptoticL2Multiplier.operator a hm.aestronglyMeasurable (Eventually.of_forall ha)).comp
        (AsymptoticHyperbolicSlash.operator (AsymptoticMobiusFold.fold (realMatrix g) n) (2*m)) := by
  rw [compactFold,operator_ofMatrix,realMatrix_foldMatrix]

#print axioms operator_ofMatrix
#print axioms operator_fold
#print axioms operator_compactFold

end AsymptoticConcreteRationalBranch
