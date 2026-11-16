module

public import QuantitativeMaassShiftedPacketDifferenceV1
public import QuantitativeMaassAbelPuncturedLimitV1
public import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The actual spectral packet associated to a compact smooth q-test. -/
def coshWavePacket (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  Wave.shiftedQuotientWavePacket N (coshTimeTest F) (coshTimeTest_waveWeight F hF R hR hs)

theorem coshWavePacket_sub (N : ℕ) (F G : ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (R : ℝ) (hR : 0≤R)
    (hsF : Function.support F⊆Iic (Real.cosh R))
    (hsG : Function.support G⊆Iic (Real.cosh R)) :
    coshWavePacket N (fun q => F q-G q) (hF.sub hG) R hR (support_sub_Iic F G _ hsF hsG)=
      coshWavePacket N F hF R hR hsF-coshWavePacket N G hG R hR hsG :=
  Wave.shiftedQuotientWavePacket_sub N (coshTimeTest F) (coshTimeTest G)
    (coshTimeTest_waveWeight F hF R hR hsF) (coshTimeTest_waveWeight G hG R hR hsG)
    (coshTimeTest_waveWeight _ (hF.sub hG) R hR (support_sub_Iic F G _ hsF hsG))

def boundaryWavePacket (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  coshWavePacket N (abelBoundaryPart F a) (abelBoundaryPart_smooth F hF a) R hR
    (abelBoundaryPart_support_source F a _ hs)

/-- The spectral error has time support of radius arcosh(1+2a), and a
uniform amplitude bounded by the original test. -/
theorem boundaryWavePacket_norm (N : ℕ) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (B : ℝ) (hB : 0≤B) (hb : ∀ q,‖F q‖≤B) (a : ℝ) (ha : 0<a) :
    ‖boundaryWavePacket N F hF R hR hs a‖≤
      (B*Real.cosh (Real.arcosh (1+2*a)/2))*(2*Real.arcosh (1+2*a)) := by
  have hq : 1≤1+2*a := by linarith
  have hs' : Function.support (abelBoundaryPart F a)⊆Iic (Real.cosh (Real.arcosh (1+2*a))) := by
    rw [Real.cosh_arcosh hq]
    exact abelBoundaryPart_support F a ha
  apply Wave.shiftedQuotientWavePacket_support_bound
  · exact Real.arcosh_nonneg hq
  · exact hB
  · exact coshTimeTest_support _ _ (Real.arcosh_nonneg hq) hs'
  · intro t
    change ‖F (Real.cosh t)*abelBoundaryCutoff a (Real.cosh t)‖≤B
    rw [norm_mul]
    exact (mul_le_mul (hb _) (abelCutoff_norm_le_one a (Real.cosh t-a)) (norm_nonneg _) hB).trans_eq
      (mul_one B)

#print axioms coshWavePacket_sub
#print axioms boundaryWavePacket_norm

end QuantitativeMaass
