module

public import FinitenessAllLevelCompactFredholmV1
public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCompactFredholm

open Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The Fredholm index is zero, by the compact homotopy from the identity. -/
theorem index_zero {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    (defect K).index = 0 := by
  let : IsBoundedSMul ℂ (X →L[ℂ] X) :=
    IsBoundedSMul.of_norm_smul_le (fun c T => ContinuousLinearMap.opNorm_smul_le c T)
  have hd : Continuous (fun z : ℂ => defect (z • K)) := by
    unfold defect
    fun_prop
  have hi : Continuous (fun z : ℂ => (defect (z • K)).index) :=
    continuous_iff_continuousAt.mpr fun z => by
      have hh : ContinuousAt (fun T : X →L[ℂ] X => T.index) (defect (z • K)) :=
        (isFredholm (K := z • K) (hK.smul z)).index_continuousAt
      exact ContinuousAt.comp (f := fun w : ℂ => defect (w • K)) hh hd.continuousAt
  have he := (inferInstance : PreconnectedSpace ℂ).constant hi (x := 1) (y := 0)
  simpa [defect] using he

#print axioms index_zero

end FinitenessAllLevelCompactFredholm
