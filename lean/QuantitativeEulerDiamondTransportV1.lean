module

public import QuantitativeEulerDiamondActionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularBranchFamily AsymptoticOrbitDecode AsymptoticCompactBranch
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- Evaluation of right multiplication moves the orbit base coordinate.
No invariance of the vector is required. -/
theorem evaluate_right_symbol (f : G → ℂ) (A : Ring) (g : G) :
    evaluate f (A*symbol g)=evaluate (fun h => f (h*g)) A := by
  induction A using MonoidAlgebra.induction_on with
  | of a =>
    change evaluate f (symbol a*symbol g)=evaluate (fun h => f (h*g)) (symbol a)
    rw [←map_mul,evaluate_symbol,evaluate_symbol]
  | add A B hA hB => simp only [add_mul,map_add,hA,hB]
  | smul c A hA => rw [smul_mul_assoc,evaluate_smul,evaluate_smul,hA]

theorem decodedEvaluation_right_symbol (ε : ℝ) (t : ℕ) (x : ℍ) (v : Space)
    (a : G) (A : Ring) (g : G) :
    decodedEvaluation ε t x v a (A*symbol g)=decodedEvaluation ε t x v (g*a) A := by
  simp only [decodedEvaluation,evaluate_right_symbol,mul_assoc]

def branchImage (b : Branch) (s : Set ℍ) : Set ℍ :=
  (fun z => ofMatrix b.matrix b.positive • z) '' s

theorem branchImage_compact (b : Branch) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact (branchImage b s) := hs.image (action_continuous _)

/-- Transport an output on the full orbit, without periodic refolding.
This is the bounded operation corresponding to right multiplication. -/
def branchTransport (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator (ofMatrix b.matrix b.positive)
    (coefficient (realMatrix b.matrix) s ε t)
    (data (realMatrix b.matrix) hs hε t).bound_nonneg
    (coefficient_norm_le _ hε t (data _ hs hε t)) x

theorem branchTransport_apply (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) (a : G) :
    branchTransport b hs hε t x v a=
      coefficient (realMatrix b.matrix) s ε t (a • x)*v (ofMatrix b.matrix b.positive*a) := rfl

theorem branchTransport_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ‖branchTransport b hs hε t x‖≤(data (realMatrix b.matrix) hs hε t).bound :=
  AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

/-- An exact bounded-operator realization of right multiplication in the
group algebra. The enlarged observation set is the actual rational image
of the original compact set. -/
theorem compactAction_mul_symbol (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (A : Ring) :
    compactAction hs hε t x (A*symbol (ofMatrix b.matrix b.positive))=
      (branchTransport b hs hε t x).comp
        (compactAction (branchImage_compact b hs) hε t x A) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  simp only [ContinuousLinearMap.comp_apply,branchTransport_apply,compactAction_decode,
    decodedEvaluation_right_symbol]
  by_cases ha : a • x∈s
  · have hb : (ofMatrix b.matrix b.positive*a) • x∈branchImage b s :=
      ⟨a • x,ha,(mul_smul _ _ _).symm⟩
    simp only [ite_eq_left ha,ite_eq_left hb,coefficient,Set.indicator_of_mem ha,ratio,
      Complex.ofReal_div]
    have hact : realMatrix b.matrix • (a • x)=(ofMatrix b.matrix b.positive*a) • x := by
      rw [mul_smul]
      exact (ofMatrix_action _ b.positive _).symm
    rw [hact]
    field_simp [cap_ne_zero hε t ((ofMatrix b.matrix b.positive*a) • x)]
  · simp only [ite_eq_right ha,coefficient,Set.indicator_of_notMem ha,zero_mul]

theorem compactAction_mul_symbol_norm (b : Branch) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (A : Ring) (v : Space) :
    ‖compactAction hs hε t x (A*symbol (ofMatrix b.matrix b.positive)) v‖≤
      (data (realMatrix b.matrix) hs hε t).bound*
        ‖compactAction (branchImage_compact b hs) hε t x A v‖ := by
  rw [compactAction_mul_symbol,ContinuousLinearMap.comp_apply]
  exact (branchTransport b hs hε t x).le_of_opNorm_le (branchTransport_norm b hs hε t x) _

#print axioms decodedEvaluation_right_symbol
#print axioms compactAction_mul_symbol
#print axioms compactAction_mul_symbol_norm
end QuantitativeEulerDiamondDecode
