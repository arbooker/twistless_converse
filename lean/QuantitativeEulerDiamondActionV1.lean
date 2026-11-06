module

public import QuantitativeEulerDiamondDecodeV1
public import AsymptoticCompactRestrictionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open scoped Classical

open UpperHalfPlane AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticOrbitDecode
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)

def symbolBranch (g : G) : Branch :=
  ⟨AsymptoticSlashGauge.representative g,
    AsymptoticRationalGroup.representative_positive g (AsymptoticSlashGauge.representative_spec g)⟩

theorem symbolBranch_label (g : G) :
    ofMatrix (symbolBranch g).matrix (symbolBranch g).positive=g := by
  apply Subtype.ext
  apply Subtype.ext
  exact AsymptoticSlashGauge.representative_spec g

/-- Every finite group-algebra expression has an actual bounded compact
operator on the original strip coordinates. The construction is linear
in the expression and uses only the existing compact branch operators. -/
def compactAction {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) : Ring →ₗ[ℂ] (Space →L[ℂ] Space) where
  toFun A := Finsupp.linearCombination ℂ (fun g => compact (symbolBranch g) hs hε t x) A.coeff
  map_add' A B := by simp only [MonoidAlgebra.coeff_add,map_add]
  map_smul' c A := by simp only [MonoidAlgebra.coeff_smul,map_smul,RingHom.id_apply]

@[simp] theorem compactAction_symbol {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (g : G) :
    compactAction hs hε t x (symbol g)=compact (symbolBranch g) hs hε t x := by
  simp [compactAction,symbol,MonoidAlgebra.of_apply]

/-- The chosen matrix representative has no effect on the operator;
any explicit positive rational matrix with the same label may be used. -/
theorem compactAction_branch {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (b : Branch) :
    compactAction hs hε t x (symbol (ofMatrix b.matrix b.positive))=compact b hs hε t x := by
  rw [compactAction_symbol]
  exact AsymptoticCompactFamilyTranslation.compact_eq_of_label _ _
    (symbolBranch_label _) hs hε t x

theorem compactAction_decode {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (A : Ring) (v : Space) (a : G) :
    compactAction hs hε t x A v a=
      if a • x∈s then (cap ε t (a • x) : ℂ)*decodedEvaluation ε t x v a A else 0 := by
  induction A using MonoidAlgebra.induction_on with
  | of g =>
    change compactAction hs hε t x (symbol g) v a=
      if a • x∈s then (cap ε t (a • x) : ℂ)*decodedEvaluation ε t x v a (symbol g) else 0
    rw [compactAction_symbol,compact_decode,symbolBranch_label,decodedEvaluation_symbol]
  | add A B hA hB =>
    simp only [map_add,_root_.add_apply,lp.coeFn_add,Pi.add_apply,hA,hB]
    by_cases ha : a • x∈s <;> simp [ha,mul_add]
  | smul c A hA =>
    simp only [map_smul,_root_.smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hA]
    change c*(if a • x∈s then _ else 0)=
      if a • x∈s then _*evaluate _ (c • A) else 0
    rw [evaluate_smul]
    by_cases ha : a • x∈s <;> simp [ha,mul_left_comm,decodedEvaluation]

#print axioms compactAction_branch
#print axioms compactAction_decode
end QuantitativeEulerDiamondDecode
