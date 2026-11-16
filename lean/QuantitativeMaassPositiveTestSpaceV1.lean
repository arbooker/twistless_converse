module

public import QuantitativeMaassSupportedAbelDistributionV1
public import Mathlib.Analysis.Distribution.TestFunction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

def positiveTimeOpen : Opens ℝ := ⟨Ioi 0,isOpen_Ioi⟩
abbrev PositiveSmoothTest := 𝓓(positiveTimeOpen,ℝ)

/-- A compact subset of positive time fits into one uniformly positive
interval. The interval is chosen from the set, independently of its tests. -/
theorem positiveCompact_interval (K : Compacts ℝ) (hK : (K:Set ℝ)⊆Ioi 0) :
    ∃ δ R : ℝ,0<δ ∧ 0≤R ∧ (K:Set ℝ)⊆Icc δ R := by
  obtain ⟨δ,hδ,hl⟩ := K.isCompact.exists_forall_le' continuous_id.continuousOn
    (fun t ht => hK ht)
  obtain ⟨R,hR⟩ := K.isCompact.bddAbove
  refine ⟨δ,max R 0,hδ,le_max_right _ _,?_⟩
  intro t ht
  exact ⟨hl t ht,(hR ht).trans (le_max_left _ _)⟩

structure PositiveCompactInterval (K : Compacts ℝ) where
  left : ℝ
  right : ℝ
  left_pos : 0<left
  right_nonneg : 0≤right
  subset : (K:Set ℝ)⊆Icc left right

def positiveCompactInterval (K : Compacts ℝ) (hK : (K:Set ℝ)⊆Ioi 0) :
    PositiveCompactInterval K := by
  classical
  let δ := Classical.choose (positiveCompact_interval K hK)
  let R := Classical.choose (Classical.choose_spec (positiveCompact_interval K hK))
  have h := Classical.choose_spec (Classical.choose_spec (positiveCompact_interval K hK))
  exact ⟨δ,R,h.1,h.2.1,h.2.2⟩

def positiveSmoothTestCompact (φ : PositiveSmoothTest) : Compacts ℝ :=
  ⟨tsupport φ,φ.hasCompactSupport⟩

def positiveSmoothTestInterval (φ : PositiveSmoothTest) :
    PositiveCompactInterval (positiveSmoothTestCompact φ) :=
  positiveCompactInterval _ φ.tsupport_subset

/-- Every ordinary real smooth test in the positive half-line is a genuine
positive-time Abel test, with support witnesses selected from its support. -/
def positiveSmoothTestToAbel (φ : PositiveSmoothTest) : PositiveTimeTest where
  toFun t := (φ t:ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp φ.contDiff
  real t := Complex.conj_ofReal _
  left := (positiveSmoothTestInterval φ).left
  right := (positiveSmoothTestInterval φ).right
  left_pos := (positiveSmoothTestInterval φ).left_pos
  right_nonneg := (positiveSmoothTestInterval φ).right_nonneg
  support := by
    intro t ht
    apply (positiveSmoothTestInterval φ).subset
    apply subset_tsupport
    intro hz
    exact ht (by simp only [hz,Complex.ofReal_zero])

/-- Changing compact support witnesses changes no test value or Abel operator. -/
theorem positiveSmoothTestToAbel_congr (N : ℕ) [NeZero N]
    (φ : PositiveSmoothTest) (ψ : PositiveTimeTest) (h : ∀ t,ψ.toFun t=(φ t:ℂ)) :
    positiveTimeAbelOperator N (positiveSmoothTestToAbel φ)=positiveTimeAbelOperator N ψ :=
  positiveTimeAbelOperator_congr N _ _ (funext (fun t => (h t).symm))

#print axioms positiveCompact_interval
#print axioms positiveSmoothTestToAbel
#print axioms positiveSmoothTestToAbel_congr

end QuantitativeMaass
