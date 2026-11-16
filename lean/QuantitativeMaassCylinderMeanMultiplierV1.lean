module

public import QuantitativeMaassCylinderRepresentativesV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeMaass

/-- Exact local restriction of a bounded height multiplier on arbitrary
cylinder L2 inputs, using actual periodic representatives. -/
theorem cylinderRestriction_multiplier (c : ℝ → ℂ) (hc : Measurable c)
    (C : ℝ) (hC : ∀ y,‖c y‖≤C) (K : Set ℍ) (hK : IsCompact K)
    (f : Lp ℂ 2 (quotientMeasure 0)) :
    cuspRestriction 0 1 K hK (cylinderAutomorphic (cylinderHeightMultiplier c hc C hC f))=
      AsymptoticL2Multiplier.operator (fun z : ℍ => c z.im)
        (hc.comp continuous_im.measurable).aestronglyMeasurable
        (Eventually.of_forall (fun z : ℍ => hC z.im))
        (cuspRestriction 0 1 K hK (cylinderAutomorphic f)) := by
  rw [←cylinderMultipliedRepresentative_class c hc C hC f,←cylinderRepresentative_class f]
  let rep := cylinderRepresentative f
  let crep := cylinderMultipliedRepresentative c hc C hC rep
  let g := cuspRestriction 0 1 K hK (AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0) rep)
  apply Lp.ext
  filter_upwards [cuspRestriction_representative_ae 0 1 K hK crep,
    cuspRestriction_representative_ae 0 1 K hK rep,
    AsymptoticL2Multiplier.operator_coeFn (fun z : ℍ => c z.im)
      (hc.comp continuous_im.measurable).aestronglyMeasurable
      (Eventually.of_forall (fun z : ℍ => hC z.im)) g] with z h1 h2 h3
  rw [h1,h3,h2]
  change c (cuspAction 1 z).im*rep.val (cuspAction 1 z)=c z.im*rep.val (cuspAction 1 z)
  simp only [cuspAction,map_one,one_smul]

/-- Height multiplication passes through the actual local horizontal mean. -/
theorem cylinderLocalMean_multiplier (c : ℝ → ℂ) (hc : Measurable c)
    (C : ℝ) (hC : ∀ y,‖c y‖≤C) (hr : ∀ y,star (c y)=c y)
    (a b : ℝ) (ha : 0<a) (f : Lp ℂ 2 (quotientMeasure 0)) :
    cylinderLocalMean a b ha (cylinderHeightMultiplier c hc C hC f)=
      AsymptoticL2Multiplier.operator c hc.aestronglyMeasurable (Eventually.of_forall hC)
        (cylinderLocalMean a b ha f) := by
  change localHeightAverage (upperRectangle 0 1 a b)
    (cuspRestriction 0 1 (upperRectangle 0 1 a b) (upperRectangle_compact 0 1 a b ha)
      (cylinderAutomorphic (cylinderHeightMultiplier c hc C hC f)))=_
  rw [cylinderRestriction_multiplier]
  exact FiberAverage.average_multiplier _ UpperHalfPlane.im continuous_im.measurable c hc C hC hr _

/-- Every bounded real measurable height cutoff preserves the genuine
nonzero-horizontal-mode subspace. -/
theorem cylinderNonzeroModes_multiplier (c : ℝ → ℂ) (hc : Measurable c)
    (C : ℝ) (hC : ∀ y,‖c y‖≤C) (hr : ∀ y,star (c y)=c y)
    {f : Lp ℂ 2 (quotientMeasure 0)} (hf : f∈cylinderNonzeroModes) :
    cylinderHeightMultiplier c hc C hC f∈cylinderNonzeroModes := by
  simp only [cylinderNonzeroModes,Submodule.mem_iInf,LinearMap.mem_ker] at hf ⊢
  intro a b ha
  change cylinderLocalMean a b ha (cylinderHeightMultiplier c hc C hC f)=0
  have hz : cylinderLocalMean a b ha f=0 := hf a b ha
  rw [cylinderLocalMean_multiplier c hc C hC hr a b ha,hz,map_zero]

#print axioms cylinderRestriction_multiplier
#print axioms cylinderLocalMean_multiplier
#print axioms cylinderNonzeroModes_multiplier

end QuantitativeMaass
