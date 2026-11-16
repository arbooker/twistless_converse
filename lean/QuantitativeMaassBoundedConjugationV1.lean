module

public import QuantitativeMaassFiniteConjugationV1
public import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

theorem finiteBandSpace_denseRange : DenseRange (finiteBandSpace μ l hl).subtype := by
  change Dense (Set.range (fun f : finiteBandSpace μ l hl => f.val))
  rw [Subtype.range_coe_subtype]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (bands_dense μ l hl)

variable (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (J : ℕ) (hT : HasBandPropagation μ l hl T J)

/-- The full bounded extension of the literal weight conjugation. Its
existence and norm estimate are derived from finite propagation, exact
orthogonal band decompositions, and density. -/
def boundedConjugation : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (conjugationLinear μ l hl T J hT).extendOfNorm (finiteBandSpace μ l hl).subtype

theorem boundedConjugation_on_finite (f : finiteBandSpace μ l hl) :
    boundedConjugation μ l hl T J hT f.val=conjugationLinear μ l hl T J hT f :=
  LinearMap.extendOfNorm_eq (finiteBandSpace_denseRange μ l hl)
    ⟨((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖,conjugationLinear_norm_bound μ l hl T J hT⟩ f

/-- The norm bound on the full actual L2 operator, independent of finite
cutoffs and without any global boundedness premise on the inverse weight. -/
theorem boundedConjugation_norm_bound :
    ‖boundedConjugation μ l hl T J hT‖≤((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖ :=
  LinearMap.opNorm_extendOfNorm_le (finiteBandSpace_denseRange μ l hl) (by positivity)
    (conjugationLinear_norm_bound μ l hl T J hT)

theorem boundedConjugation_coeFn (f : finiteBandSpace μ l hl) :
    boundedConjugation μ l hl T J hT f.val=ᵐ[μ]
      (fun x => (Real.exp (l x):ℂ)*(T (exponentialEnd μ l hl (-1) f).val) x) := by
  rw [boundedConjugation_on_finite]
  have h := exponentialEnd_coeFn μ l hl 1
    (finitePropagationMap μ l hl T J hT (exponentialEnd μ l hl (-1) f))
  simpa only [one_mul] using! h

theorem boundedConjugation_unique (B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hB : ∀ f : finiteBandSpace μ l hl,B f.val=conjugationLinear μ l hl T J hT f) :
    boundedConjugation μ l hl T J hT=B := by
  apply LinearMap.extendOfNorm_unique (finiteBandSpace_denseRange μ l hl)
    (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1)*‖T‖)
    (conjugationLinear_norm_bound μ l hl T J hT)
  apply LinearMap.ext
  intro f
  exact hB f

#print axioms finiteBandSpace_denseRange
#print axioms boundedConjugation_on_finite
#print axioms boundedConjugation_norm_bound
#print axioms boundedConjugation_coeFn
#print axioms boundedConjugation_unique

end QuantitativeMaass.LogBands
