module

public import AsymptoticRegularCompactBranchV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularCompactBranch

open UpperHalfPlane AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticCompactBranch (Data coefficient)
open AsymptoticMassTransport (strip)

/-- The input strip selects exactly one integer fold. This holds for
every counting-space vector, without imposing an individual functional
equation or periodicity on the output. -/
theorem operator_selected (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t)
    (x : ℍ) (f : Space) (a : AsymptoticRationalGroup.Group) :
    operator g hg hε t D x f a=
      coefficient (realMatrix g) s ε t (a • x)*
        f (compactFold g hg (Int.floor (realMatrix g • (a • x)).re)*a) := by
  classical
  rw [operator_apply]
  by_cases ha : a • x∈s
  · let n := Int.floor (realMatrix g • (a • x)).re
    rw [Finset.sum_eq_single n]
    · rw [AsymptoticOrbitDiagonal.corner_apply]
      have hn : (compactFold g hg n*a) • x∈strip := by
        rw [mul_smul,compactFold_action,AsymptoticMobiusFold.fold_mem_strip_iff]
      rw [ite_eq_left hn]
    · intro m hm hmn
      have hn : (compactFold g hg m*a) • x∉strip := by
        rw [mul_smul,compactFold_action,AsymptoticMobiusFold.fold_mem_strip_iff]
        exact hmn
      rw [AsymptoticOrbitDiagonal.corner_apply,ite_eq_right hn,mul_zero]
    · exact fun hn => (hn (D.fold_mem (a • x) ha)).elim
  · simp only [coefficient,Set.indicator_of_notMem ha,zero_mul,Finset.sum_const_zero]

/-- Enlarging the finite fold certificate or changing its auxiliary
bounds leaves the concrete compact operator unchanged. -/
theorem operator_data_independent (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D E : Data (realMatrix g) s ε t) (x : ℍ) :
    operator g hg hε t D x=operator g hg hε t E x := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  rw [operator_selected,operator_selected]

/-- A compact observation already has its stated output cutoff. -/
theorem operator_left_corner (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data (realMatrix g) s ε t) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp (operator g hg hε t D x)=operator g hg hε t D x := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext a
  change AsymptoticOrbitDiagonal.corner s x (operator g hg hε t D x f) a=_
  rw [AsymptoticOrbitDiagonal.corner_apply,operator_selected]
  by_cases ha : a • x∈s
  · rw [ite_eq_left ha]
  · rw [ite_eq_right ha,coefficient,Set.indicator_of_notMem ha,zero_mul]

#print axioms operator_selected
#print axioms operator_data_independent
#print axioms operator_left_corner

end AsymptoticRegularCompactBranch
