module

public import QuantitativeMaassPositiveTimeSeminormV1
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

def positiveTimeCompact (δ R : ℝ) : Compacts ℝ := ⟨Icc δ R,isCompact_Icc⟩

abbrev SupportedTimeTest (δ R : ℝ) := 𝓓_{positiveTimeCompact δ R}(ℝ,ℝ)

def supportedPositiveTimeTest (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (φ : SupportedTimeTest δ R) : PositiveTimeTest where
  toFun t := (φ t:ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp φ.contDiff
  real t := Complex.conj_ofReal _
  left := δ
  right := R
  left_pos := hδ
  right_nonneg := hR
  support := by
    intro t ht
    apply φ.support_subset
    intro hz
    exact ht (by simp only [hz,Complex.ofReal_zero])

theorem supportedPositiveTimeTest_deriv (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (φ : SupportedTimeTest δ R) (t : ℝ) :
    deriv (supportedPositiveTimeTest δ R hδ hR φ).toFun t=((deriv (φ : ℝ → ℝ) t:ℝ):ℂ) :=
  ((φ.contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv

theorem supportedPositiveTimeTest_deriv_bound (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (φ : SupportedTimeTest δ R) (t : ℝ) :
    ‖deriv (supportedPositiveTimeTest δ R hδ hR φ).toFun t‖≤
      ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ (positiveTimeCompact δ R) 1 φ := by
  rw [supportedPositiveTimeTest_deriv,Complex.norm_real,Real.norm_eq_abs,
    ← Real.norm_eq_abs,norm_deriv_eq_norm_fderiv,← norm_iteratedFDeriv_one]
  exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ (by simp)

/-- Literal Abel operator of a real smooth test in one fixed positive compact
interval. This definition imposes no spectral representation. -/
def supportedTimeAbelOperator (N : ℕ) [NeZero N] (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R)
    (φ : SupportedTimeTest δ R) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  positiveTimeAbelOperator N (supportedPositiveTimeTest δ R hδ hR φ)

theorem supportedTimeAbelOperator_scaledSub (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ ψ : SupportedTimeTest δ R) (c : ℝ) :
    supportedTimeAbelOperator N δ R hδ hR (c • φ-ψ)=
      c • supportedTimeAbelOperator N δ R hδ hR φ-supportedTimeAbelOperator N δ R hδ hR ψ := by
  have he : (supportedPositiveTimeTest δ R hδ hR (c • φ-ψ)).toFun=
      ((supportedPositiveTimeTest δ R hδ hR φ).scaledSub
        (supportedPositiveTimeTest δ R hδ hR ψ) c).toFun := by
    funext t
    change ((c*φ t-ψ t:ℝ):ℂ)=(c:ℂ)*(φ t:ℂ)-(ψ t:ℂ)
    push_cast
    rfl
  unfold supportedTimeAbelOperator
  rw [positiveTimeAbelOperator_congr N _ _ he,positiveTimeAbelOperator_scaledSub]
  rfl

theorem supportedTimeAbelOperator_bound (N : ℕ) [NeZero N]
    (δ R : ℝ) (hδ : 0<δ) (hR : 0≤R) (φ : SupportedTimeTest δ R) :
    ‖supportedTimeAbelOperator N δ R hδ hR φ‖≤positiveTimeNormConstant δ R*
      ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ (positiveTimeCompact δ R) 1 φ :=
  positiveTimeAbelOperator_norm_common N (supportedPositiveTimeTest δ R hδ hR φ)
    δ R _ hδ hR (supportedPositiveTimeTest δ R hδ hR φ).support
    (supportedPositiveTimeTest_deriv_bound δ R hδ hR φ)

#print axioms supportedPositiveTimeTest_deriv_bound
#print axioms supportedTimeAbelOperator_scaledSub
#print axioms supportedTimeAbelOperator_bound

end QuantitativeMaass
