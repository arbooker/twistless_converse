module

public import QuantitativeMaassWindowTailsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace QuantitativeMaass

/-- Separation from a symmetric trimmed window grows with distance from the
positive centre, also for its reflected negative interval. -/
theorem shrunken_symmetric_shell_separation (t ε δ r u : ℝ)
    (ht : 0≤t) (hr : 0≤r) (hε : ε≤1) (hδ : 0≤δ)
    (hu : u∈Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) :
    |r-t|-1≤|r-u| := by
  rcases hu with hu|hu
  · have hclose : |u-t|≤1 := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have htri := abs_sub_le r u t
    linarith
  · have hrt : |r-t|≤r+t := abs_le.mpr ⟨by linarith,by linarith⟩
    have hru := le_abs_self (r-u)
    linarith [hu.2]

/-- On distant frequency shells the actual squared trimmed-window multiplier
has every even power of decay in R*(d-1). -/
theorem shrunken_squaredWindow_shell_tail (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (t ε δ R r d : ℝ) (ht : 0≤t) (hr : 0≤r) (hε : ε≤1) (hδ : 0≤δ)
    (hR : 0<R) (hd : 1<d) (hsep : d≤|r-t|) (k : ℕ) :
    (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) r)^2≤
      (∫ u,|u|^k*K u)^2/(R*(d-1))^(2*k) := by
  apply squaredWindow_distance_tail K hK R hR _ (measurableSet_Icc.union measurableSet_Icc)
    r (d-1) (by linarith) _ k
  intro u hu
  exact (by linarith : d-1≤|r-t|-1).trans
    (shrunken_symmetric_shell_separation t ε δ r u ht hr hε hδ hu)

#print axioms shrunken_symmetric_shell_separation
#print axioms shrunken_squaredWindow_shell_tail

end QuantitativeMaass
