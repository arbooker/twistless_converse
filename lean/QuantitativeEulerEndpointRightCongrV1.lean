module

public import QuantitativeEulerEndpointProjectiveCheckV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode AsymptoticRationalBranches
open AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- An identity valid on every compact observation set remains valid after
every right symbol, via the actual branch transport on its image set. -/
theorem compact_right_symbol_congr (A B : Ring) (g : G)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ)
    (h : ∀ {u : Set ℍ} (hu : IsCompact u), compactAction hu hε t x A=compactAction hu hε t x B)
    {s : Set ℍ} (hs : IsCompact s) :
    compactAction hs hε t x (A*symbol g)=compactAction hs hε t x (B*symbol g) := by
  have ha := compactAction_mul_symbol (symbolBranch g) hs hε t x A
  have hb := compactAction_mul_symbol (symbolBranch g) hs hε t x B
  rw [symbolBranch_label] at ha hb
  exact ha.trans ((congrArg (fun T : Space →L[ℂ] Space =>
    (branchTransport (symbolBranch g) hs hε t x).comp T)
    (h (branchImage_compact (symbolBranch g) hs))).trans hb.symm)

/-- The same exact identity is stable under an arbitrary finite ring
multiplier. No invariance or norm premise is introduced. -/
theorem compact_right_multiplier_congr (A B E : Ring)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ)
    (h : ∀ {u : Set ℍ} (hu : IsCompact u), compactAction hu hε t x A=compactAction hu hε t x B)
    {s : Set ℍ} (hs : IsCompact s) :
    compactAction hs hε t x (A*E)=compactAction hs hε t x (B*E) := by
  rw [compact_expression_right_expand,compact_expression_right_expand]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun T : Space →L[ℂ] Space => E.coeff g • T)
    (compact_right_symbol_congr A B g hε t x h hs)

#print axioms compact_right_symbol_congr
#print axioms compact_right_multiplier_congr
end QuantitativeEulerEndpointPrepared
