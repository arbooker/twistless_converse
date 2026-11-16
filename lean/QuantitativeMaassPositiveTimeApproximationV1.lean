module

public import QuantitativeMaassPositiveCoshTestV1
public import QuantitativeMaassAbelPuncturedLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelPuncturedTest_real (F : ℝ → ℂ) (hr : ∀ q,star (F q)=F q) (a q : ℝ) :
    star (F q-abelBoundaryPart F a q)=F q-abelBoundaryPart F a q := by
  simp only [abelBoundaryPart,abelBoundaryCutoff,abelCutoff,star_sub,star_mul,hr,
    Complex.star_def,Complex.conj_ofReal]
  ring

theorem abelPuncturedTest_zero_interval (F : ℝ → ℂ) (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (q : ℝ) (hq : q∈Icc 1 (Real.cosh (Real.arcosh (1+a)))) :
    F q-abelBoundaryPart F a q=0 := by
  rw [Real.cosh_arcosh (by linarith : 1≤1+a)] at hq
  exact abelBoundaryPart_sub_zero_near F a ha ha1 q hq.1 hq.2

/-- An explicit positive-time test for the actual punctured Abel operator. -/
def abelPuncturedPositiveTest (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    PositiveTimeTest :=
  positiveTimeTestOfCosh (fun q => F q-abelBoundaryPart F a q)
    (hF.sub (abelBoundaryPart_smooth F hF a)) (abelPuncturedTest_real F hr a)
    (Real.arcosh (1+a)) R (Real.arcosh_pos (by linarith)) hR
    (abelPuncturedTest_zero_interval F a ha ha1)
    (support_sub_Iic F (abelBoundaryPart F a) _ hs (abelBoundaryPart_support_source F a _ hs))

theorem abelPuncturedPositiveTest_operator (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    positiveTimeAbelOperator N (abelPuncturedPositiveTest F hF hr R hR hs a ha ha1)=
      abelPuncturedOperator N F hF hc R hR hs a :=
  positiveTimeTestOfCosh_operator N (fun q => F q-abelBoundaryPart F a q)
    (hF.sub (abelBoundaryPart_smooth F hF a)) (hc.sub (abelBoundaryPart_compact F hc a))
    (abelPuncturedTest_real F hr a) (Real.arcosh (1+a)) R (Real.arcosh_pos (by linarith)) hR
    (abelPuncturedTest_zero_interval F a ha ha1)
    (support_sub_Iic F (abelBoundaryPart F a) _ hs (abelBoundaryPart_support_source F a _ hs))

/-- Every real smooth compact q-test operator is an operator-norm limit of
explicit genuine positive-time test operators. No spectral identity is assumed. -/
theorem abelPuncturedPositiveTest_tendsto {ι : Type*} (l : Filter ι)
    (N : ℕ) [NeZero N] (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hr : ∀ q,star (F q)=F q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha1 : ∀ i,a i≤1) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => positiveTimeAbelOperator N
      (abelPuncturedPositiveTest F hF hr R hR hs (a i) (ha i) (ha1 i))) l
      (𝓝 (abelKernelOperator N F hF hc R hR hs)) := by
  have h := abelPuncturedOperator_tendsto l N F hF hc R hR hs a ha ha1 ha0
  apply h.congr'
  filter_upwards with i
  exact (abelPuncturedPositiveTest_operator N F hF hc hr R hR hs (a i) (ha i) (ha1 i)).symm

#print axioms abelPuncturedTest_real
#print axioms abelPuncturedPositiveTest_operator
#print axioms abelPuncturedPositiveTest_tendsto

end QuantitativeMaass
